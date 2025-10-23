package main

import (
	"bytes"
	"compress/gzip"
	"context"
	"crypto/rand"
	"crypto/tls"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net/http"
	"net/http/cookiejar"
	"os"
	"os/signal"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

const (
	BurstCount          = 10
	TargetInterval      = 100 * time.Millisecond
	MaxReqPerSecond     = 20
	APIActiveHour       = 6
	APICutoffHour       = 12
	VerificationEndHour = 8
	RequestTimeout      = 5 * time.Second
	WhatsAppRetries     = 3
	WhatsAppDelay       = 2 * time.Second
	WhatsAppRetryDelay  = 5 * time.Second
	OTPTimeout          = 5 * time.Minute
	MaxResponseSize     = 10 * 1024 * 1024
	DefaultTimezone     = "Asia/Kolkata"
	TokenRefreshBuffer  = 30 * time.Minute
	MaxRetryAttempts    = 3
	RetryDelay          = 2 * time.Second
	MinPhoneDigits      = 10
	MaxPhoneDigits      = 15
)

var verificationMinutes = []int{0, 30}

type Config struct {
	AuthToken        string `json:"auth_token"`
	RefreshToken     string `json:"refresh_token"`
	HipID            string `json:"hip_id"`
	TargetDate       string `json:"target_date"`
	WhatsAppAPIKey   string `json:"whatsapp_api_key"`
	WhatsAppEndpoint string `json:"whatsapp_endpoint"`
	SuccessPhone     string `json:"success_phone"`
	ErrorPhone       string `json:"error_phone"`
	Timezone         string `json:"timezone,omitempty"`
}

func (c *Config) Validate() error {
	if c.AuthToken == "" {
		return fmt.Errorf("auth_token is required")
	}
	if c.RefreshToken == "" {
		return fmt.Errorf("refresh_token is required")
	}
	if c.HipID == "" {
		return fmt.Errorf("hip_id is required")
	}
	if c.Timezone == "" {
		c.Timezone = DefaultTimezone
	}
	if _, err := time.LoadLocation(c.Timezone); err != nil {
		return fmt.Errorf("invalid timezone '%s': %v", c.Timezone, err)
	}
	if c.TargetDate != "" {
		if _, err := time.Parse("2006-01-02", c.TargetDate); err != nil {
			return fmt.Errorf("invalid target_date format (expected YYYY-MM-DD): %v", err)
		}
	}
	if c.WhatsAppEndpoint != "" && !strings.HasPrefix(c.WhatsAppEndpoint, "http") {
		return fmt.Errorf("invalid whatsapp_endpoint: must be a valid URL")
	}
	return nil
}

type Token struct {
	Auth      string
	Sess      string
	Refresh   string
	DeviceID  string
	ExpiresAt time.Time
}

func (t *Token) IsExpired() bool {
	return t.ExpiresAt.Before(time.Now().Add(TokenRefreshBuffer))
}

type Patient struct {
	OID       string   `json:"oid"`
	FLN       string   `json:"fln"`
	HealthIDs []string `json:"health-ids"`
	ABHA      string   `json:"abha"`
}

func (p *Patient) PrimaryHealthID() string {
	if len(p.HealthIDs) > 0 {
		return p.HealthIDs[0]
	}
	return ""
}

type ValidatedPatient struct {
	Patient        Patient
	ValidationDone bool
}

type BurstResult struct {
	Attempt      int    `json:"attempt"`
	Timestamp    string `json:"timestamp"`
	Status       string `json:"status"`
	ResponseTime int64  `json:"response_time_ms"`
	TokenNumber  string `json:"token_number,omitempty"`
	Error        string `json:"error,omitempty"`
}

type PatientSummary struct {
	Patient       Patient `json:"patient"`
	TotalAttempts int     `json:"total_attempts"`
	Successful    int     `json:"successful"`
	ValidationOK  bool    `json:"validation_success"`
	TokenNumber   string  `json:"token_number,omitempty"`
	ExecutionTime string  `json:"execution_time"`
	GoldenAttempt int     `json:"golden_attempt,omitempty"`
}

type VerificationResult struct {
	Patient     Patient
	TokenNumber string
	HasSuccess  bool
	Timestamp   string
}

type HTTPClient interface {
	Do(req *http.Request) (*http.Response, error)
}

type TokenManager interface {
	GetMasterToken() *Token
	RefreshMasterToken() error
	GetPatientToken(patientOID string) (*Token, error)
}

type NotificationService interface {
	SendNotification(phone, message string) error
}

type RateLimiter interface {
	Acquire() <-chan struct{}
	Close()
}

type ResultWriter struct {
	baseDir   string
	mu        sync.Mutex
	fileCache map[string]*os.File
}

func NewResultWriter(baseDir string) (*ResultWriter, error) {
	if err := os.MkdirAll(baseDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create results directory: %v", err)
	}

	return &ResultWriter{
		baseDir:   baseDir,
		fileCache: make(map[string]*os.File),
	}, nil
}

func (rw *ResultWriter) WritePatientDir(healthID string) (string, error) {
	rw.mu.Lock()
	defer rw.mu.Unlock()

	healthIDSafe := sanitizeFilename(strings.Split(healthID, "@")[0])
	patientDir := filepath.Join(rw.baseDir, healthIDSafe)

	if err := os.MkdirAll(patientDir, 0755); err != nil {
		return "", fmt.Errorf("failed to create patient directory: %v", err)
	}

	return patientDir, nil
}

func (rw *ResultWriter) WriteBurstResult(patientDir string, result BurstResult) error {
	if result.Status != "error" && result.Status != "mismatch" {
		return nil
	}

	path := filepath.Join(patientDir, fmt.Sprintf("attempt_%03d.json", result.Attempt))
	return writeJSONFile(path, result)
}

func (rw *ResultWriter) WriteSummary(patientDir string, summary PatientSummary) error {
	path := filepath.Join(patientDir, "summary.json")
	return writeJSONFile(path, summary)
}

func (rw *ResultWriter) WriteExecutionSummary(summary map[string]interface{}) error {
	path := filepath.Join(rw.baseDir, "execution_summary.json")
	return writeJSONFile(path, summary)
}

func (rw *ResultWriter) Close() {
	rw.mu.Lock()
	defer rw.mu.Unlock()

	for _, file := range rw.fileCache {
		file.Close()
	}
}

type tokenBucket struct {
	ch       chan struct{}
	ticker   *time.Ticker
	ctx      context.Context
	cancel   context.CancelFunc
	wg       sync.WaitGroup
	closedMu sync.Mutex
	closed   bool
}

func NewRateLimiter(rps int, ctx context.Context) RateLimiter {
	rateLimiterCtx, cancel := context.WithCancel(ctx)
	ch := make(chan struct{}, rps)

	for i := 0; i < rps; i++ {
		ch <- struct{}{}
	}

	ticker := time.NewTicker(time.Second / time.Duration(rps))

	tb := &tokenBucket{
		ch:     ch,
		ticker: ticker,
		ctx:    rateLimiterCtx,
		cancel: cancel,
	}

	tb.wg.Add(1)
	go func() {
		defer tb.wg.Done()
		defer ticker.Stop()
		for {
			select {
			case <-rateLimiterCtx.Done():
				return
			case <-ticker.C:
				tb.closedMu.Lock()
				if !tb.closed {
					select {
					case ch <- struct{}{}:
					default:
					}
				}
				tb.closedMu.Unlock()
			}
		}
	}()

	return tb
}

func (tb *tokenBucket) Acquire() <-chan struct{} {
	return tb.ch
}

func (tb *tokenBucket) Close() {
	tb.closedMu.Lock()
	if tb.closed {
		tb.closedMu.Unlock()
		return
	}
	tb.closed = true
	tb.closedMu.Unlock()

	tb.cancel()
	tb.wg.Wait()
	close(tb.ch)
}

type ABDMManager struct {
	config          *Config
	tokenManager    TokenManager
	httpClient      HTTPClient
	rateLimiter     RateLimiter
	notificationSvc NotificationService
	validatedPool   []*ValidatedPatient
	originalTokens  map[string]string
	tokenMutex      sync.RWMutex
	tokenMapMutex   sync.RWMutex
	resultWriter    *ResultWriter
	successCount    atomic.Int32
	totalCount      atomic.Int32
	ctx             context.Context
	cancel          context.CancelFunc
}

type defaultTokenManager struct {
	masterToken *Token
	httpClient  HTTPClient
	config      *Config
	mutex       sync.RWMutex
}

func (tm *defaultTokenManager) GetMasterToken() *Token {
	tm.mutex.RLock()
	defer tm.mutex.RUnlock()
	return tm.masterToken
}

func (tm *defaultTokenManager) RefreshMasterToken() error {
	tm.mutex.Lock()
	defer tm.mutex.Unlock()

	payload := map[string]string{
		"sess":    tm.masterToken.Auth,
		"refresh": tm.masterToken.Refresh,
	}

	var lastErr error
	for attempt := 1; attempt <= MaxRetryAttempts; attempt++ {
		body, status, err := tm.makeHTTPCall("POST", "https://aortago.eka.care/phr/v3/auth/refresh", payload)
		if err == nil && status == 200 {
			var respObj map[string]interface{}
			if err := json.Unmarshal(body, &respObj); err != nil {
				lastErr = fmt.Errorf("failed to parse refresh response: %v", err)
				continue
			}

			sess, sessOk := respObj["sess"].(string)
			refresh, refreshOk := respObj["refresh"].(string)

			if !sessOk || !refreshOk || sess == "" || refresh == "" {
				lastErr = fmt.Errorf("invalid refresh response format: missing or empty sess/refresh tokens")
				continue
			}

			deviceID, err := generateSecureUUID()
			if err != nil {
				lastErr = fmt.Errorf("failed to generate device ID: %v", err)
				continue
			}

			tm.masterToken = &Token{
				Auth:      sess,
				Sess:      sess,
				Refresh:   refresh,
				DeviceID:  deviceID,
				ExpiresAt: parseJWTExpiry(sess),
			}

			log.Println("Master token refreshed successfully")
			return nil
		}

		lastErr = fmt.Errorf("refresh attempt %d failed [POST /phr/v3/auth/refresh]: status %d, error: %v", attempt, status, err)
		if attempt < MaxRetryAttempts {
			time.Sleep(RetryDelay * time.Duration(attempt))
		}
	}

	return fmt.Errorf("master token refresh failed after %d attempts: %v", MaxRetryAttempts, lastErr)
}

func (tm *defaultTokenManager) GetPatientToken(patientOID string) (*Token, error) {
	masterToken := tm.GetMasterToken()
	if masterToken.IsExpired() {
		if err := tm.RefreshMasterToken(); err != nil {
			return nil, fmt.Errorf("failed to refresh master token for patient switch: %v", err)
		}
		masterToken = tm.GetMasterToken()
	}

	payload := map[string]string{
		"oid":     patientOID,
		"refresh": masterToken.Refresh,
	}

	body, status, err := tm.makeHTTPCall("POST", "https://aortago.eka.care/v3/auth/switch", payload)
	if err != nil || status != 200 {
		return nil, fmt.Errorf("patient switch failed [POST /v3/auth/switch] for OID %s: status %d, error: %v", patientOID, status, err)
	}

	var switchResponse map[string]string
	if err := json.Unmarshal(body, &switchResponse); err != nil {
		return nil, fmt.Errorf("failed to parse switch response for OID %s: %v", patientOID, err)
	}

	sess, sessOk := switchResponse["sess"]
	refresh, refreshOk := switchResponse["refresh"]
	if !sessOk || !refreshOk || sess == "" || refresh == "" {
		return nil, fmt.Errorf("invalid switch response for OID %s: missing or empty sess/refresh", patientOID)
	}

	deviceID, err := generateSecureUUID()
	if err != nil {
		return nil, fmt.Errorf("failed to generate device ID for OID %s: %v", patientOID, err)
	}

	return &Token{
		Auth:      sess,
		Sess:      sess,
		Refresh:   refresh,
		DeviceID:  deviceID,
		ExpiresAt: parseJWTExpiry(sess),
	}, nil
}

func (tm *defaultTokenManager) makeHTTPCall(method, url string, payload interface{}) ([]byte, int, error) {
	var body []byte
	if payload != nil {
		var err error
		body, err = json.Marshal(payload)
		if err != nil {
			return nil, 0, fmt.Errorf("failed to marshal payload: %v", err)
		}
	}

	ctx, cancel := context.WithTimeout(context.Background(), RequestTimeout)
	defer cancel()

	req, err := http.NewRequestWithContext(ctx, method, url, bytes.NewReader(body))
	if err != nil {
		return nil, 0, fmt.Errorf("failed to create request [%s %s]: %v", method, url, err)
	}

	headers := buildBaseHeaders()
	headers["auth"] = tm.masterToken.Auth
	headers["Cookie"] = fmt.Sprintf("sess=%s; refresh=%s", tm.masterToken.Sess, tm.masterToken.Refresh)
	headers["device-id"] = tm.masterToken.DeviceID

	for k, v := range headers {
		req.Header.Set(k, v)
	}

	resp, err := tm.httpClient.Do(req)
	if err != nil {
		return nil, 0, fmt.Errorf("request failed [%s %s]: %v", method, url, err)
	}
	defer resp.Body.Close()

	respBody, err := readLimitedResponse(resp, MaxResponseSize)
	return respBody, resp.StatusCode, err
}

type whatsAppService struct {
	apiKey   string
	endpoint string
	client   HTTPClient
}

func (ws *whatsAppService) SendNotification(phone, message string) error {
	if ws.apiKey == "" || ws.endpoint == "" {
		return fmt.Errorf("WhatsApp configuration missing")
	}

	var lastErr error
	for attempt := 1; attempt <= WhatsAppRetries; attempt++ {
		err := ws.sendMessage(phone, message)
		if err == nil {
			if attempt > 1 {
				log.Printf("WhatsApp message sent successfully on attempt %d", attempt)
			}
			return nil
		}

		lastErr = err
		log.Printf("WhatsApp attempt %d/%d failed: %v", attempt, WhatsAppRetries, err)

		if attempt < WhatsAppRetries {
			time.Sleep(WhatsAppRetryDelay)
		}
	}

	return fmt.Errorf("failed after %d attempts: %v", WhatsAppRetries, lastErr)
}

func (ws *whatsAppService) sendMessage(phone, message string) error {
	payload := map[string]interface{}{
		"message": message,
	}

	if strings.Contains(phone, "@c.us") || strings.Contains(phone, "@g.us") {
		payload["chatId"] = phone
	} else {
		formattedPhone := formatPhoneNumber(phone)
		if formattedPhone != "" {
			payload["chatId"] = formattedPhone
		} else {
			return fmt.Errorf("invalid phone number format: %s", phone)
		}
	}

	jsonData, err := json.Marshal(payload)
	if err != nil {
		return fmt.Errorf("failed to marshal WhatsApp payload: %v", err)
	}

	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()

	req, err := http.NewRequestWithContext(ctx, "POST", ws.endpoint, bytes.NewBuffer(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create WhatsApp request: %v", err)
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("x-api-key", ws.apiKey)
	req.Header.Set("Accept", "application/json")

	resp, err := ws.client.Do(req)
	if err != nil {
		return fmt.Errorf("WhatsApp request failed: %v", err)
	}
	defer resp.Body.Close()

	respBody, err := readLimitedResponse(resp, MaxResponseSize)
	if err != nil {
		return fmt.Errorf("failed to read WhatsApp response: %v", err)
	}

	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		return fmt.Errorf("WhatsApp API error %d: %s", resp.StatusCode, sanitizeForLog(string(respBody)))
	}

	log.Printf("WhatsApp API response (%d): %s", resp.StatusCode, sanitizeForLog(string(respBody)))
	return nil
}

func NewABDMManager(config *Config, ctx context.Context) (*ABDMManager, error) {
	if err := config.Validate(); err != nil {
		return nil, fmt.Errorf("config validation failed: %v", err)
	}

	jar, err := cookiejar.New(nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create cookie jar: %v", err)
	}

	httpClient := &http.Client{
		Timeout: 10 * time.Second,
		Jar:     jar,
		Transport: &http.Transport{
			TLSClientConfig:     &tls.Config{InsecureSkipVerify: false},
			MaxIdleConns:        100,
			MaxIdleConnsPerHost: 10,
			IdleConnTimeout:     90 * time.Second,
			DisableCompression:  true,
			ForceAttemptHTTP2:   true,
		},
	}

	deviceID, err := generateSecureUUID()
	if err != nil {
		return nil, fmt.Errorf("failed to generate device ID: %v", err)
	}

	masterToken := &Token{
		Auth:      config.AuthToken,
		Sess:      config.AuthToken,
		Refresh:   config.RefreshToken,
		DeviceID:  deviceID,
		ExpiresAt: parseJWTExpiry(config.AuthToken),
	}

	tokenManager := &defaultTokenManager{
		masterToken: masterToken,
		httpClient:  httpClient,
		config:      config,
	}

	rateLimiter := NewRateLimiter(MaxReqPerSecond, ctx)

	notificationSvc := &whatsAppService{
		apiKey:   config.WhatsAppAPIKey,
		endpoint: config.WhatsAppEndpoint,
		client:   httpClient,
	}

	resultsDir := fmt.Sprintf("results_%s", time.Now().Format("20060102_150405"))
	resultWriter, err := NewResultWriter(resultsDir)
	if err != nil {
		return nil, fmt.Errorf("failed to initialize result writer: %v", err)
	}

	managerCtx, managerCancel := context.WithCancel(ctx)

	return &ABDMManager{
		config:          config,
		tokenManager:    tokenManager,
		httpClient:      httpClient,
		rateLimiter:     rateLimiter,
		notificationSvc: notificationSvc,
		validatedPool:   make([]*ValidatedPatient, 0),
		originalTokens:  make(map[string]string),
		resultWriter:    resultWriter,
		ctx:             managerCtx,
		cancel:          managerCancel,
	}, nil
}

func (am *ABDMManager) Close() {
	am.cancel()
	am.rateLimiter.Close()
	am.resultWriter.Close()

	successCount := am.successCount.Load()
	totalCount := am.totalCount.Load()

	if totalCount == 0 {
		log.Println("No executions performed")
		return
	}

	successRate := (float64(successCount) / float64(totalCount)) * 100

	executionSummary := map[string]interface{}{
		"total_patients":    totalCount,
		"successful":        successCount,
		"failed":            totalCount - successCount,
		"success_rate":      fmt.Sprintf("%.1f%%", successRate),
		"completion_time":   time.Now().Format(time.RFC3339),
		"validated_pool":    len(am.validatedPool),
		"total_token_calls": totalCount * BurstCount,
	}

	if err := am.resultWriter.WriteExecutionSummary(executionSummary); err != nil {
		log.Printf("Failed to write execution summary: %v", err)
	}

	log.Printf("Results saved to: %s | Success rate: %.1f%% (%d/%d)",
		am.resultWriter.baseDir, successRate, successCount, totalCount)
}

func (am *ABDMManager) initializeSystem() error {
	log.Println("Initializing system...")

	masterToken := am.tokenManager.GetMasterToken()
	if masterToken.IsExpired() {
		if err := am.tokenManager.RefreshMasterToken(); err != nil {
			return fmt.Errorf("failed to refresh master token during initialization: %v", err)
		}
	}

	log.Println("System ready")
	return nil
}

func (am *ABDMManager) fetchPatients() ([]Patient, error) {
	var lastErr error
	for attempt := 1; attempt <= MaxRetryAttempts; attempt++ {
		body, status, err := am.makeHTTPCall("GET", "https://aortago.eka.care/profiles/v1/patient", nil)

		if err == nil && status == 200 {
			var patients []Patient
			if err := json.Unmarshal(body, &patients); err != nil {
				lastErr = fmt.Errorf("failed to parse patients response: %v", err)
				continue
			}
			log.Printf("Fetched %d patients successfully", len(patients))
			return patients, nil
		}

		if status == 401 {
			log.Printf("Token expired, refreshing... (attempt %d/%d)", attempt, MaxRetryAttempts)
			if refreshErr := am.tokenManager.RefreshMasterToken(); refreshErr != nil {
				return nil, fmt.Errorf("token refresh failed on attempt %d: %v", attempt, refreshErr)
			}
			continue
		}

		lastErr = fmt.Errorf("patient fetch failed [GET /profiles/v1/patient]: status %d, error: %v", status, err)
		if attempt < MaxRetryAttempts {
			time.Sleep(RetryDelay * time.Duration(attempt))
		}
	}

	return nil, fmt.Errorf("failed to fetch patients after %d attempts: %v", MaxRetryAttempts, lastErr)
}

func (am *ABDMManager) makeHTTPCall(method, url string, payload interface{}) ([]byte, int, error) {
	var body []byte
	if payload != nil {
		var err error
		body, err = json.Marshal(payload)
		if err != nil {
			return nil, 0, fmt.Errorf("failed to marshal payload: %v", err)
		}
	}

	ctx, cancel := context.WithTimeout(am.ctx, RequestTimeout)
	defer cancel()

	req, err := http.NewRequestWithContext(ctx, method, url, bytes.NewReader(body))
	if err != nil {
		return nil, 0, fmt.Errorf("failed to create request [%s %s]: %v", method, url, err)
	}

	masterToken := am.tokenManager.GetMasterToken()
	headers := buildBaseHeaders()
	headers["auth"] = masterToken.Auth
	headers["Cookie"] = fmt.Sprintf("sess=%s; refresh=%s", masterToken.Sess, masterToken.Refresh)
	headers["device-id"] = masterToken.DeviceID

	for k, v := range headers {
		req.Header.Set(k, v)
	}

	resp, err := am.httpClient.Do(req)
	if err != nil {
		return nil, 0, fmt.Errorf("request failed [%s %s]: %v", method, url, err)
	}
	defer resp.Body.Close()

	respBody, err := readLimitedResponse(resp, MaxResponseSize)
	return respBody, resp.StatusCode, err
}

func (am *ABDMManager) validatePatientsSequential(patients []Patient) error {
	log.Printf("Starting sequential validation for %d patients", len(patients))

	for i, patient := range patients {
		if patient.PrimaryHealthID() == "" {
			log.Printf("Patient %d/%d: %s - No health IDs, skipping", i+1, len(patients), sanitizeForLog(patient.FLN))
			continue
		}

		log.Printf("Validating patient %d/%d: %s", i+1, len(patients), sanitizeForLog(patient.FLN))

		validationToken, err := am.tokenManager.GetPatientToken(patient.OID)
		if err != nil {
			log.Printf("Switch failed for %s: %v", sanitizeForLog(patient.FLN), err)
			continue
		}

		hipAccessGranted := am.checkHIPAccess(validationToken)

		if !hipAccessGranted {
			log.Printf("Patient %s requires OTP authentication", sanitizeForLog(patient.FLN))
			if err := am.performOTPAuth(validationToken, patient.PrimaryHealthID()); err != nil {
				log.Printf("OTP authentication failed for %s: %v", sanitizeForLog(patient.FLN), err)
				continue
			}

			if !am.checkHIPAccess(validationToken) {
				log.Printf("HIP access still denied for %s after OTP", sanitizeForLog(patient.FLN))
				continue
			}
		}

		am.validatedPool = append(am.validatedPool, &ValidatedPatient{
			Patient:        patient,
			ValidationDone: true,
		})

		log.Printf("Patient %s validated successfully", sanitizeForLog(patient.FLN))
	}

	log.Printf("Validation complete: %d/%d patients validated", len(am.validatedPool), len(patients))
	return nil
}

func (am *ABDMManager) checkHIPAccess(token *Token) bool {
	url := fmt.Sprintf("https://ndhm.eka.care/v1/hip/providers/search?hip_id=%s", am.config.HipID)
	_, status, _ := am.makeHTTPCallWithToken("GET", url, nil, token)

	log.Printf("HIP access check: status %d", status)
	return status == 200
}

func (am *ABDMManager) performOTPAuth(token *Token, healthID string) error {
	initPayload := map[string]string{
		"auth_method": "MOBILE_OTP",
		"health_id":   healthID,
	}

	initBody, initStatus, err := am.makeHTTPCallWithToken("POST", "https://ndhm.eka.care/v1/auth/init", initPayload, token)
	if err != nil || initStatus != 200 {
		return fmt.Errorf("OTP initialization failed [POST /v1/auth/init]: status %d, error: %v", initStatus, err)
	}

	var initResponse map[string]string
	if err := json.Unmarshal(initBody, &initResponse); err != nil {
		return fmt.Errorf("failed to parse OTP init response: %v", err)
	}

	txnID, exists := initResponse["txn_id"]
	if !exists || txnID == "" {
		return fmt.Errorf("OTP init response missing txn_id")
	}

	fmt.Printf("\n🔐 OTP required for patient: %s\n", sanitizeForDisplay(healthID))
	fmt.Print("Enter the OTP you received: ")

	otpChan := make(chan string, 1)
	errChan := make(chan error, 1)

	go func() {
		var otp string
		_, err := fmt.Scanln(&otp)
		if err != nil {
			errChan <- fmt.Errorf("failed to read OTP: %v", err)
			return
		}
		otpChan <- otp
	}()

	var otp string
	select {
	case otp = <-otpChan:
	case err := <-errChan:
		return err
	case <-time.After(OTPTimeout):
		return fmt.Errorf("OTP input timeout after %v", OTPTimeout)
	case <-am.ctx.Done():
		return fmt.Errorf("operation cancelled")
	}

	verifyPayload := map[string]string{
		"otp":       otp,
		"health_id": healthID,
		"txn_id":    txnID,
	}

	_, verifyStatus, err := am.makeHTTPCallWithToken("POST", "https://ndhm.eka.care/v1/auth/verify", verifyPayload, token)
	if err != nil || verifyStatus != 200 {
		return fmt.Errorf("OTP verification failed [POST /v1/auth/verify]: status %d, error: %v", verifyStatus, err)
	}

	log.Printf("OTP verification successful for %s", sanitizeForLog(healthID))
	return nil
}

func (am *ABDMManager) makeHTTPCallWithToken(method, url string, payload interface{}, token *Token) ([]byte, int, error) {
	var body []byte
	if payload != nil {
		var err error
		body, err = json.Marshal(payload)
		if err != nil {
			return nil, 0, fmt.Errorf("failed to marshal payload: %v", err)
		}
	}

	ctx, cancel := context.WithTimeout(am.ctx, RequestTimeout)
	defer cancel()

	req, err := http.NewRequestWithContext(ctx, method, url, bytes.NewReader(body))
	if err != nil {
		return nil, 0, fmt.Errorf("failed to create request [%s %s]: %v", method, url, err)
	}

	headers := buildBaseHeaders()
	headers["auth"] = token.Auth
	headers["Cookie"] = fmt.Sprintf("sess=%s; refresh=%s", token.Sess, token.Refresh)
	headers["device-id"] = token.DeviceID

	for k, v := range headers {
		req.Header.Set(k, v)
	}

	resp, err := am.httpClient.Do(req)
	if err != nil {
		return nil, 0, fmt.Errorf("request failed [%s %s]: %v", method, url, err)
	}
	defer resp.Body.Close()

	respBody, err := readLimitedResponse(resp, MaxResponseSize)
	return respBody, resp.StatusCode, err
}

func (am *ABDMManager) executeWithFreshTokens(targetTime time.Time) error {
	if len(am.validatedPool) == 0 {
		return fmt.Errorf("no validated patients to execute")
	}

	isImmediate := targetTime.Before(time.Now().Add(30 * time.Second))

	if !isImmediate {
		log.Printf("Target execution time: %s", targetTime.Format("15:04:05"))

		freshTokenTime := targetTime.Add(-30 * time.Second)
		if waitUntil := time.Until(freshTokenTime); waitUntil > 0 {
			log.Printf("Waiting until %s for fresh token generation...", freshTokenTime.Format("15:04:05"))
			select {
			case <-time.After(waitUntil):
			case <-am.ctx.Done():
				return fmt.Errorf("operation cancelled")
			}
		}

		tokenMap, err := am.generateFreshTokensConcurrent()
		if err != nil {
			return fmt.Errorf("failed to generate fresh tokens: %v", err)
		}

		if finalWait := time.Until(targetTime); finalWait > 0 {
			log.Printf("Fresh tokens ready, waiting %.1f seconds for execution...", finalWait.Seconds())
			select {
			case <-time.After(finalWait):
			case <-am.ctx.Done():
				return fmt.Errorf("operation cancelled")
			}
		}

		return am.executeConcurrentBursts(tokenMap)
	} else {
		log.Println("Immediate execution - generating fresh tokens now")
		tokenMap, err := am.generateFreshTokensConcurrent()
		if err != nil {
			return fmt.Errorf("failed to generate fresh tokens: %v", err)
		}
		return am.executeConcurrentBursts(tokenMap)
	}
}

func (am *ABDMManager) generateFreshTokensConcurrent() (map[string]*Token, error) {
	log.Printf("Generating fresh execution tokens concurrently for %d validated patients", len(am.validatedPool))

	var wg sync.WaitGroup
	var mu sync.Mutex
	tokenMap := make(map[string]*Token)
	errorCount := 0

	for _, validated := range am.validatedPool {
		wg.Add(1)
		go func(vp *ValidatedPatient) {
			defer wg.Done()

			freshToken, err := am.tokenManager.GetPatientToken(vp.Patient.OID)
			if err != nil {
				log.Printf("Fresh token generation failed for %s: %v", sanitizeForLog(vp.Patient.FLN), err)
				mu.Lock()
				errorCount++
				mu.Unlock()
				return
			}

			mu.Lock()
			tokenMap[vp.Patient.OID] = freshToken
			mu.Unlock()

			log.Printf("Fresh token generated for %s", sanitizeForLog(vp.Patient.FLN))
		}(validated)
	}

	wg.Wait()

	if errorCount > 0 {
		log.Printf("Fresh token generation completed with %d errors", errorCount)
	}

	log.Printf("Fresh token generation complete: %d/%d tokens ready", len(tokenMap), len(am.validatedPool))
	return tokenMap, nil
}

func (am *ABDMManager) executeConcurrentBursts(tokenMap map[string]*Token) error {
	log.Printf("Starting concurrent execution for %d patients at %s", len(tokenMap), time.Now().Format("15:04:05.000"))

	type executionResult struct {
		patient       Patient
		successCount  int
		tokenNumber   string
		goldenAttempt int
	}

	results := make(chan executionResult, len(am.validatedPool))
	var burstWg sync.WaitGroup

	for _, validated := range am.validatedPool {
		token, exists := tokenMap[validated.Patient.OID]
		if !exists {
			log.Printf("Skipping %s - no execution token available", sanitizeForLog(validated.Patient.FLN))
			continue
		}

		burstWg.Add(1)
		go func(patient Patient, execToken *Token) {
			defer burstWg.Done()

			am.totalCount.Add(1)

			successCount, tokenNumber, goldenAttempt := am.performBurstExecutionWithImmediateNotification(patient, execToken)

			results <- executionResult{
				patient:       patient,
				successCount:  successCount,
				tokenNumber:   tokenNumber,
				goldenAttempt: goldenAttempt,
			}
		}(validated.Patient, token)
	}

	go func() {
		burstWg.Wait()
		close(results)
	}()

	for result := range results {
		patientDir, err := am.resultWriter.WritePatientDir(result.patient.PrimaryHealthID())
		if err != nil {
			log.Printf("Failed to create patient directory for %s: %v", sanitizeForLog(result.patient.FLN), err)
			continue
		}

		summary := PatientSummary{
			Patient:       result.patient,
			TotalAttempts: BurstCount,
			Successful:    result.successCount,
			ValidationOK:  result.successCount > 0,
			TokenNumber:   result.tokenNumber,
			ExecutionTime: time.Now().Format(time.RFC3339),
			GoldenAttempt: result.goldenAttempt,
		}

		if err := am.resultWriter.WriteSummary(patientDir, summary); err != nil {
			log.Printf("Failed to save summary for %s: %v", sanitizeForLog(result.patient.FLN), err)
		}

		if result.successCount > 0 {
			am.successCount.Add(1)
		}

		if result.tokenNumber != "" {
			am.tokenMutex.Lock()
			am.originalTokens[result.patient.PrimaryHealthID()] = result.tokenNumber
			am.tokenMutex.Unlock()
		}

		log.Printf("Completed %s: %d/%d successful", sanitizeForLog(result.patient.FLN), result.successCount, BurstCount)
	}

	return am.runVerificationLoop(tokenMap)
}

func (am *ABDMManager) performBurstExecutionWithImmediateNotification(patient Patient, token *Token) (int, string, int) {
	payload := map[string]interface{}{
		"location":  map[string]interface{}{},
		"hip_id":    am.config.HipID,
		"hip_code":  am.config.HipID,
		"health_id": patient.PrimaryHealthID(),
	}

	successCount := 0
	var goldenToken string
	var goldenResponseBytes []byte
	goldenAttempt := 0
	notificationSent := false

	for i := 0; i < BurstCount; i++ {
		select {
		case <-am.rateLimiter.Acquire():
		case <-am.ctx.Done():
			break
		}

		start := time.Now()
		response, status, err := am.makeHTTPCallWithToken("POST", "https://ndhm.eka.care/v2/hip/profile/share", payload, token)
		elapsed := time.Since(start)

		if err != nil || status != 200 {
			continue
		}

		if i >= 2 && goldenToken == "" {
			tokenNum, hasValidToken := extractAndValidateTokenNumber(response)
			if hasValidToken {
				goldenToken = tokenNum
				goldenResponseBytes = response
				goldenAttempt = i + 1
				successCount++
				log.Printf("Golden response detected at attempt %d for %s: token %s", i+1, sanitizeForLog(patient.FLN), tokenNum)

				if !notificationSent {
					go am.sendImmediateNotification(patient, tokenNum, true)
					notificationSent = true
				}
			}
		} else if goldenToken != "" {
			if areJSONResponsesBytesEqual(response, goldenResponseBytes) {
				successCount++
			}
		}

		if i < BurstCount-1 {
			if sleepTime := TargetInterval - elapsed; sleepTime > 0 {
				select {
				case <-time.After(sleepTime):
				case <-am.ctx.Done():
					break
				}
			}
		}
	}

	if !notificationSent && successCount == 0 {
		go am.sendImmediateNotification(patient, "", false)
	}

	return successCount, goldenToken, goldenAttempt
}

func (am *ABDMManager) sendImmediateNotification(patient Patient, tokenNumber string, hasSuccess bool) {
	if am.config.WhatsAppAPIKey == "" || am.config.WhatsAppEndpoint == "" {
		return
	}

	var message, phone string

	if hasSuccess {
		if tokenNumber != "" {
			message = fmt.Sprintf("✅ SUCCESS - %s\nToken Number: %s\nTime: %s",
				sanitizeForDisplay(patient.FLN), tokenNumber, time.Now().Format("15:04:05"))
			phone = am.config.SuccessPhone
			log.Printf("Sending immediate success notification for %s with token: %s", sanitizeForLog(patient.FLN), tokenNumber)
		} else {
			message = fmt.Sprintf("⚠️ PARTIAL SUCCESS - %s\nResponse received but no token number found\nTime: %s",
				sanitizeForDisplay(patient.FLN), time.Now().Format("15:04:05"))
			phone = am.config.ErrorPhone
			log.Printf("Sending immediate partial success notification for %s", sanitizeForLog(patient.FLN))
		}
	} else {
		message = fmt.Sprintf("❌ FAILED - %s\nNo successful response received\nTime: %s",
			sanitizeForDisplay(patient.FLN), time.Now().Format("15:04:05"))
		phone = am.config.ErrorPhone
		log.Printf("Sending immediate failure notification for %s", sanitizeForLog(patient.FLN))
	}

	if phone != "" {
		if err := am.notificationSvc.SendNotification(phone, message); err != nil {
			log.Printf("Failed to send immediate notification for %s: %v", sanitizeForLog(patient.FLN), err)
		}
	}
}

func (am *ABDMManager) runVerificationLoop(tokenMap map[string]*Token) error {
	am.tokenMutex.RLock()
	hasTokens := len(am.originalTokens) > 0
	am.tokenMutex.RUnlock()

	if !hasTokens {
		log.Println("No original tokens to verify, skipping verification loop")
		return nil
	}

	log.Println("Starting verification loop for token stability...")

	loc, err := time.LoadLocation(am.config.Timezone)
	if err != nil {
		return fmt.Errorf("failed to load timezone %s: %v", am.config.Timezone, err)
	}

	now := time.Now().In(loc)

verificationLoop:
	for hour := APIActiveHour; hour <= VerificationEndHour; hour++ {
		for _, minute := range verificationMinutes {
			if hour == VerificationEndHour && minute > 0 {
				break verificationLoop
			}

			targetTime := time.Date(now.Year(), now.Month(), now.Day(), hour, minute, 0, 0, loc)

			if targetTime.Before(time.Now()) {
				continue
			}

			log.Printf("Next verification scheduled at %s", targetTime.Format("15:04:05"))

			select {
			case <-time.After(time.Until(targetTime)):
			case <-am.ctx.Done():
				return fmt.Errorf("verification cancelled")
			}

			log.Printf("Running verification at %s", time.Now().Format("15:04:05"))
			changes, err := am.performVerificationCheck(tokenMap)
			if err != nil {
				log.Printf("Verification check failed: %v", err)
				continue
			}

			if len(changes) > 0 {
				log.Printf("Token changes detected! Sending updated notifications...")
				am.sendVerificationNotifications(changes)
				log.Println("Verification complete - changes detected, exiting...")
				return nil
			}

			log.Printf("Verification complete - all tokens stable")
		}
	}

	log.Println("Verification loop complete - all tokens remained stable until 8:00")
	return nil
}

func (am *ABDMManager) performVerificationCheck(tokenMap map[string]*Token) ([]VerificationResult, error) {
	var changes []VerificationResult

	for _, validated := range am.validatedPool {
		if validated.Patient.PrimaryHealthID() == "" {
			continue
		}

		healthID := validated.Patient.PrimaryHealthID()

		am.tokenMutex.RLock()
		originalToken, exists := am.originalTokens[healthID]
		am.tokenMutex.RUnlock()

		if !exists {
			continue
		}

		am.tokenMapMutex.RLock()
		token, tokenExists := tokenMap[validated.Patient.OID]
		am.tokenMapMutex.RUnlock()

		if !tokenExists {
			log.Printf("No token available for verification of %s", sanitizeForLog(validated.Patient.FLN))
			continue
		}

		if token.IsExpired() {
			refreshedToken, err := am.tokenManager.GetPatientToken(validated.Patient.OID)
			if err != nil {
				log.Printf("Failed to refresh token for verification of %s: %v", sanitizeForLog(validated.Patient.FLN), err)
				continue
			}
			token = refreshedToken
			am.tokenMapMutex.Lock()
			tokenMap[validated.Patient.OID] = refreshedToken
			am.tokenMapMutex.Unlock()
		}

		currentToken, hasSuccess := am.performSingleVerificationBurst(validated.Patient, token)

		if hasSuccess && currentToken != "" && currentToken != originalToken {
			log.Printf("Token changed for %s: %s → %s", sanitizeForLog(validated.Patient.FLN), originalToken, currentToken)
			changes = append(changes, VerificationResult{
				Patient:     validated.Patient,
				TokenNumber: currentToken,
				HasSuccess:  true,
				Timestamp:   time.Now().Format("15:04:05"),
			})

			am.tokenMutex.Lock()
			am.originalTokens[healthID] = currentToken
			am.tokenMutex.Unlock()
		} else if hasSuccess && currentToken == originalToken {
			log.Printf("Token stable for %s: %s", sanitizeForLog(validated.Patient.FLN), currentToken)
		} else {
			log.Printf("Verification failed for %s", sanitizeForLog(validated.Patient.FLN))
		}

		select {
		case <-time.After(500 * time.Millisecond):
		case <-am.ctx.Done():
			return changes, fmt.Errorf("verification cancelled")
		}
	}

	return changes, nil
}

func (am *ABDMManager) performSingleVerificationBurst(patient Patient, token *Token) (string, bool) {
	payload := map[string]interface{}{
		"location":  map[string]interface{}{},
		"hip_id":    am.config.HipID,
		"hip_code":  am.config.HipID,
		"health_id": patient.PrimaryHealthID(),
	}

	select {
	case <-am.rateLimiter.Acquire():
	case <-am.ctx.Done():
		return "", false
	}

	response, status, err := am.makeHTTPCallWithToken("POST", "https://ndhm.eka.care/v2/hip/profile/share", payload, token)

	if err != nil || status != 200 {
		return "", false
	}

	tokenNumber := extractTokenNumber(response)
	return tokenNumber, tokenNumber != ""
}

func (am *ABDMManager) sendVerificationNotifications(changes []VerificationResult) {
	if am.config.WhatsAppAPIKey == "" || am.config.WhatsAppEndpoint == "" {
		log.Println("WhatsApp configuration missing, skipping verification notifications")
		return
	}

	for i, change := range changes {
		if am.ctx.Err() != nil {
			log.Println("Context cancelled, stopping verification notifications")
			break
		}

		message := fmt.Sprintf("🔄 TOKEN UPDATED - %s\nNew Token Number: %s\nTime: %s\n⚠️ Previous token was replaced by backend",
			sanitizeForDisplay(change.Patient.FLN), change.TokenNumber, change.Timestamp)

		phone := am.config.SuccessPhone
		if phone != "" {
			if err := am.notificationSvc.SendNotification(phone, message); err != nil {
				log.Printf("Verification notification failed for %s: %v", sanitizeForLog(change.Patient.FLN), err)
			} else {
				log.Printf("Verification notification sent for %s with new token: %s", sanitizeForLog(change.Patient.FLN), change.TokenNumber)
			}
		}

		if i < len(changes)-1 {
			select {
			case <-time.After(WhatsAppDelay):
			case <-am.ctx.Done():
				return
			}
		}
	}
}

func main() {
	fmt.Println("\n🚀 ABDM Profile Share - Optimized Flow")
	fmt.Println("=====================================\n")

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	signalChan := make(chan os.Signal, 1)
	signal.Notify(signalChan, os.Interrupt, syscall.SIGTERM)

	go func() {
		<-signalChan
		log.Println("\nReceived shutdown signal, cleaning up...")
		cancel()
	}()

	config, err := loadConfig()
	if err != nil {
		log.Fatalf("Config error: %v", err)
	}

	manager, err := NewABDMManager(config, ctx)
	if err != nil {
		log.Fatalf("Manager creation error: %v", err)
	}
	defer manager.Close()

	if err := manager.initializeSystem(); err != nil {
		log.Fatalf("System initialization error: %v", err)
	}

	patients, err := manager.fetchPatients()
	if err != nil {
		log.Fatalf("Failed to fetch patients: %v", err)
	}

	selectedPatients, err := selectPatients(patients)
	if err != nil {
		log.Fatalf("Patient selection error: %v", err)
	}

	if len(selectedPatients) == 0 {
		log.Println("No patients selected")
		return
	}

	if err := manager.validatePatientsSequential(selectedPatients); err != nil {
		log.Fatalf("Patient validation error: %v", err)
	}

	targetTime, err := calculateExecutionTime(config.TargetDate, config.Timezone)
	if err != nil {
		log.Fatalf("Target time calculation error: %v", err)
	}

	if err := manager.executeWithFreshTokens(targetTime); err != nil {
		log.Fatalf("Execution error: %v", err)
	}
}

func loadConfig() (*Config, error) {
	data, err := os.ReadFile("config.json")
	if err != nil {
		return nil, fmt.Errorf("failed to read config file: %v", err)
	}

	var config Config
	if err := json.Unmarshal(data, &config); err != nil {
		return nil, fmt.Errorf("failed to parse config: %v", err)
	}

	return &config, nil
}

func generateSecureUUID() (string, error) {
	b := make([]byte, 16)
	if _, err := rand.Read(b); err != nil {
		return "", fmt.Errorf("failed to generate random bytes: %v", err)
	}
	return fmt.Sprintf("%X-%X-%X-%X-%X", b[0:4], b[4:6], b[6:8], b[8:10], b[10:]), nil
}

func parseJWTExpiry(token string) time.Time {
	parts := strings.Split(token, ".")
	if len(parts) != 3 {
		log.Printf("Invalid JWT format: expected 3 parts, got %d", len(parts))
		return time.Time{}
	}

	payload, err := base64.RawURLEncoding.DecodeString(parts[1])
	if err != nil {
		log.Printf("Failed to decode JWT payload: %v", err)
		return time.Time{}
	}

	var claims map[string]interface{}
	if err := json.Unmarshal(payload, &claims); err != nil {
		log.Printf("Failed to parse JWT claims: %v", err)
		return time.Time{}
	}

	if exp, ok := claims["exp"].(float64); ok {
		return time.Unix(int64(exp), 0)
	}

	log.Printf("JWT missing exp claim")
	return time.Time{}
}

func calculateExecutionTime(targetDate, timezone string) (time.Time, error) {
	loc, err := time.LoadLocation(timezone)
	if err != nil {
		return time.Time{}, fmt.Errorf("failed to load timezone %s: %v", timezone, err)
	}

	now := time.Now().In(loc)
	currentHour := now.Hour()

	if targetDate != "" {
		parsed, err := time.ParseInLocation("2006-01-02", targetDate, loc)
		if err != nil {
			return time.Time{}, fmt.Errorf("invalid target date format: %v", err)
		}

		target := time.Date(parsed.Year(), parsed.Month(), parsed.Day(), APIActiveHour, 0, 0, 0, loc)

		if parsed.Format("2006-01-02") == now.Format("2006-01-02") && currentHour >= APIActiveHour && currentHour < APICutoffHour {
			return now, nil
		}

		if target.After(now) {
			return target, nil
		}

		return target.Add(24 * time.Hour), nil
	}

	if currentHour < APIActiveHour {
		return time.Date(now.Year(), now.Month(), now.Day(), APIActiveHour, 0, 0, 0, loc), nil
	} else if currentHour < APICutoffHour {
		return now, nil
	}

	return time.Date(now.Year(), now.Month(), now.Day(), APIActiveHour, 0, 0, 0, loc).Add(24 * time.Hour), nil
}

func selectPatients(patients []Patient) ([]Patient, error) {
	if len(patients) == 0 {
		return nil, fmt.Errorf("no patients available")
	}

	fmt.Println("\n👥 Available Patients:")
	fmt.Println(strings.Repeat("-", 60))
	for i, patient := range patients {
		fmt.Printf("%d. %s (OID: %s)", i+1, sanitizeForDisplay(patient.FLN), patient.OID)
		if patient.PrimaryHealthID() != "" {
			fmt.Printf(" (%s)", sanitizeForDisplay(patient.PrimaryHealthID()))
		}
		fmt.Println()
	}

	fmt.Print("\nSelect patients (e.g., 1,2): ")
	var input string
	if _, err := fmt.Scanln(&input); err != nil {
		return nil, fmt.Errorf("failed to read input: %v", err)
	}

	var selected []Patient
	for _, s := range strings.Split(input, ",") {
		s = strings.TrimSpace(s)
		idx, err := strconv.Atoi(s)
		if err != nil {
			log.Printf("Invalid selection: %s", s)
			continue
		}

		if idx < 1 || idx > len(patients) {
			log.Printf("Selection out of range: %d", idx)
			continue
		}

		selected = append(selected, patients[idx-1])
	}

	if len(selected) == 0 {
		return nil, fmt.Errorf("no valid patients selected")
	}

	return selected, nil
}

func writeJSONFile(path string, data interface{}) error {
	jsonData, err := json.MarshalIndent(data, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal JSON: %v", err)
	}

	if err := os.WriteFile(path, jsonData, 0644); err != nil {
		return fmt.Errorf("failed to write file %s: %v", path, err)
	}

	return nil
}

func extractTokenNumber(jsonData []byte) string {
	if jsonData == nil {
		return ""
	}

	var responseMap map[string]interface{}
	if err := json.Unmarshal(jsonData, &responseMap); err != nil {
		return ""
	}

	if tokenNumber, ok := responseMap["token_number"].(string); ok && tokenNumber != "" {
		return tokenNumber
	}

	if data, ok := responseMap["data"].(map[string]interface{}); ok {
		if tokenNumber, ok := data["token_number"].(string); ok && tokenNumber != "" {
			return tokenNumber
		}
	}

	return ""
}

func extractAndValidateTokenNumber(jsonData []byte) (string, bool) {
	if jsonData == nil {
		return "", false
	}

	var responseMap map[string]interface{}
	if err := json.Unmarshal(jsonData, &responseMap); err != nil {
		return "", false
	}

	if tokenNumber, ok := responseMap["token_number"].(string); ok && tokenNumber != "" {
		return tokenNumber, true
	}

	if data, ok := responseMap["data"].(map[string]interface{}); ok {
		if tokenNumber, ok := data["token_number"].(string); ok && tokenNumber != "" {
			return tokenNumber, true
		}
	}

	return "", false
}

func areJSONResponsesBytesEqual(resp1, resp2 []byte) bool {
	if resp1 == nil || resp2 == nil {
		return false
	}

	var map1, map2 map[string]interface{}
	if err := json.Unmarshal(resp1, &map1); err != nil {
		return false
	}
	if err := json.Unmarshal(resp2, &map2); err != nil {
		return false
	}

	return jsonMapsEqual(map1, map2)
}

func jsonMapsEqual(m1, m2 map[string]interface{}) bool {
	if len(m1) != len(m2) {
		return false
	}

	for k, v1 := range m1 {
		v2, exists := m2[k]
		if !exists {
			return false
		}

		switch v1Type := v1.(type) {
		case map[string]interface{}:
			v2Map, ok := v2.(map[string]interface{})
			if !ok || !jsonMapsEqual(v1Type, v2Map) {
				return false
			}
		case []interface{}:
			v2Slice, ok := v2.([]interface{})
			if !ok || !jsonSlicesEqual(v1Type, v2Slice) {
				return false
			}
		default:
			if fmt.Sprint(v1) != fmt.Sprint(v2) {
				return false
			}
		}
	}

	return true
}

func jsonSlicesEqual(s1, s2 []interface{}) bool {
	if len(s1) != len(s2) {
		return false
	}

	for i := range s1 {
		switch v1 := s1[i].(type) {
		case map[string]interface{}:
			v2, ok := s2[i].(map[string]interface{})
			if !ok || !jsonMapsEqual(v1, v2) {
				return false
			}
		case []interface{}:
			v2, ok := s2[i].([]interface{})
			if !ok || !jsonSlicesEqual(v1, v2) {
				return false
			}
		default:
			if fmt.Sprint(s1[i]) != fmt.Sprint(s2[i]) {
				return false
			}
		}
	}

	return true
}

func formatPhoneNumber(phone string) string {
	if phone == "" {
		return ""
	}

	if strings.Contains(phone, "@c.us") || strings.Contains(phone, "@g.us") {
		return phone
	}

	re := regexp.MustCompile(`[^\d+]`)
	cleanPhone := re.ReplaceAllString(phone, "")

	if strings.HasPrefix(cleanPhone, "+") {
		cleanPhone = cleanPhone[1:]
	}

	if len(cleanPhone) < MinPhoneDigits || len(cleanPhone) > MaxPhoneDigits {
		return ""
	}

	return cleanPhone + "@c.us"
}

func buildBaseHeaders() map[string]string {
	return map[string]string{
		"flavour":         "ios",
		"version":         "3.1.3",
		"client-id":       "patient-app-ios",
		"locale":          "en",
		"make":            "Apple",
		"model":           "iPhone",
		"model-version":   "iPhone 13 Pro Max",
		"User-Agent":      "EkaCare/3.1.3 (com.orbi.eka.care; build:1; iOS 19.0.0) Alamofire/5.10.2",
		"Accept":          "*/*",
		"Accept-Language": "en-US;q=1.0, hi-US;q=0.9",
		"Accept-Encoding": "gzip, deflate",
		"Content-Type":    "application/json",
	}
}

func readLimitedResponse(resp *http.Response, maxSize int64) ([]byte, error) {
	var reader io.Reader = resp.Body

	if resp.Header.Get("Content-Encoding") == "gzip" {
		gzipReader, err := gzip.NewReader(resp.Body)
		if err != nil {
			return nil, fmt.Errorf("failed to create gzip reader: %v", err)
		}
		defer gzipReader.Close()
		reader = gzipReader
	}

	limitedReader := io.LimitReader(reader, maxSize)
	data, err := io.ReadAll(limitedReader)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %v", err)
	}

	return data, nil
}

func sanitizeForLog(input string) string {
	if len(input) > 50 {
		return input[:47] + "..."
	}
	return input
}

func sanitizeForDisplay(input string) string {
	return strings.ReplaceAll(input, "\n", " ")
}

func sanitizeFilename(input string) string {
	re := regexp.MustCompile(`[^a-zA-Z0-9._-]`)
	return re.ReplaceAllString(input, "_")
}
