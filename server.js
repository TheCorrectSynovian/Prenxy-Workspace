const express = require('express');
const cors = require('cors');
const path = require('path');
const fs = require('fs');
const fsp = require('fs/promises');
const multer = require('multer');
const archiver = require('archiver');
const os = require('os');
const crypto = require('crypto');
const { promisify } = require('util');
const { execFile } = require('child_process');

const app = express();
const PORT = 3000;
const WEB_RESTART_ENABLED = String(process.env.ALLOW_WEB_RESTART || '').toLowerCase() === 'true';
const execFileAsync = promisify(execFile);
const CONVERT_TEMP_DIR = path.join(os.tmpdir(), 'prenxy-convert-cache');

// ════════════════════════════════════════════════════════════════════════════
//  SECURE STORAGE LAYOUT
//  .internal_root/
//    .credentials.enc    — AES-256-GCM encrypted user database
//    .master.key          — randomly generated master encryption key
//    <sha256(username)>/  — per-user document folders (hashed for security)
// ════════════════════════════════════════════════════════════════════════════
const INTERNAL_ROOT = path.join(__dirname, '.internal_root');
const CREDENTIALS_FILE = path.join(INTERNAL_ROOT, '.credentials.enc');
const MASTER_KEY_FILE = path.join(INTERNAL_ROOT, '.master.key');
const SOCIAL_FILE = path.join(INTERNAL_ROOT, '.social.enc');
const APPROVALS_FILE = path.join(INTERNAL_ROOT, '.approvals.enc');
const CHAT_FILE = path.join(INTERNAL_ROOT, '.chat.enc');
const AVATARS_DIR = path.join(INTERNAL_ROOT, '.avatars');
const STAGING_DIR = path.join(INTERNAL_ROOT, '.staging');
const MEDIA_DIR = path.join(INTERNAL_ROOT, '.media');
const CHAT_ATTACHMENTS_DIR = path.join(INTERNAL_ROOT, '.chat_attachments');
const CLASSROOM_FILE = path.join(INTERNAL_ROOT, '.classroom.enc');
const ACTION_LOG_FILE = path.join(INTERNAL_ROOT, '.actions.log');

function logInfo(message) {
  const ts = new Date().toISOString();
  console.log(`[${ts}] INFO  ${message}`);
}

function logWarn(message) {
  const ts = new Date().toISOString();
  console.warn(`[${ts}] WARN  ${message}`);
}

function logError(message) {
  const ts = new Date().toISOString();
  console.error(`[${ts}] ERROR ${message}`);
}

function writeActionLog(action, details = {}, actor = 'system') {
  try {
    if (!fs.existsSync(INTERNAL_ROOT)) fs.mkdirSync(INTERNAL_ROOT, { recursive: true });
    const row = {
      timestamp: new Date().toISOString(),
      actor,
      action,
      details
    };
    fs.appendFileSync(ACTION_LOG_FILE, JSON.stringify(row) + '\n', 'utf8');
  } catch (e) {
    logWarn(`Action log write failed: ${e.message}`);
  }
}

function readActionLogs(limit = 50) {
  if (!fs.existsSync(ACTION_LOG_FILE)) return [];
  const raw = fs.readFileSync(ACTION_LOG_FILE, 'utf8');
  const lines = raw.split('\n').filter(Boolean);
  const parsed = [];
  for (const line of lines) {
    try { parsed.push(JSON.parse(line)); } catch {}
  }
  return parsed.slice(-Math.max(1, Math.min(Number(limit) || 50, 500)));
}

// ═══════ Crypto helpers ═══════
const PBKDF2_ITERATIONS = 100000;
const PBKDF2_KEYLEN = 64;
const PBKDF2_DIGEST = 'sha512';

function hashUsername(username) {
  return crypto.createHash('sha256').update(username.toLowerCase().trim()).digest('hex');
}

function hashPassword(password, salt) {
  if (!salt) salt = crypto.randomBytes(32).toString('hex');
  const hash = crypto.pbkdf2Sync(password, salt, PBKDF2_ITERATIONS, PBKDF2_KEYLEN, PBKDF2_DIGEST).toString('hex');
  return { hash, salt };
}

function verifyPassword(password, storedHash, salt) {
  const { hash } = hashPassword(password, salt);
  return crypto.timingSafeEqual(Buffer.from(hash, 'hex'), Buffer.from(storedHash, 'hex'));
}

function getMasterKey() {
  if (!fs.existsSync(MASTER_KEY_FILE)) {
    const key = crypto.randomBytes(32);
    fs.writeFileSync(MASTER_KEY_FILE, key.toString('hex'), 'utf8');
    try { fs.chmodSync(MASTER_KEY_FILE, 0o600); } catch {}
    return key;
  }
  return Buffer.from(fs.readFileSync(MASTER_KEY_FILE, 'utf8').trim(), 'hex');
}

function encryptData(plaintext, key) {
  const iv = crypto.randomBytes(16);
  const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);
  let encrypted = cipher.update(plaintext, 'utf8', 'hex');
  encrypted += cipher.final('hex');
  const tag = cipher.getAuthTag().toString('hex');
  return iv.toString('hex') + ':' + tag + ':' + encrypted;
}

function decryptData(ciphertext, key) {
  const parts = ciphertext.split(':');
  if (parts.length !== 3) throw new Error('Invalid encrypted data format');
  const iv = Buffer.from(parts[0], 'hex');
  const tag = Buffer.from(parts[1], 'hex');
  const encrypted = parts[2];
  const decipher = crypto.createDecipheriv('aes-256-gcm', key, iv);
  decipher.setAuthTag(tag);
  let decrypted = decipher.update(encrypted, 'hex', 'utf8');
  decrypted += decipher.final('utf8');
  return decrypted;
}

// ═══════ Encrypted user database ═══════
function loadUsers() {
  if (!fs.existsSync(CREDENTIALS_FILE)) return {};
  try {
    const encrypted = fs.readFileSync(CREDENTIALS_FILE, 'utf8').trim();
    const key = getMasterKey();
    const json = decryptData(encrypted, key);
    return JSON.parse(json);
  } catch (e) {
    console.error('Failed to decrypt credentials:', e.message);
    return {};
  }
}

function saveUsers(users) {
  const key = getMasterKey();
  const json = JSON.stringify(users, null, 2);
  const encrypted = encryptData(json, key);
  fs.writeFileSync(CREDENTIALS_FILE, encrypted, 'utf8');
  try { fs.chmodSync(CREDENTIALS_FILE, 0o600); } catch {}
}

// ═══════ Social data (encrypted) ═══════
const SOCIAL_DEFAULTS = { posts: [], follows: {}, friendRequests: [], friends: {}, reports: [], bookmarks: {} };
function loadSocialData() {
  if (!fs.existsSync(SOCIAL_FILE)) return JSON.parse(JSON.stringify(SOCIAL_DEFAULTS));
  try {
    const encrypted = fs.readFileSync(SOCIAL_FILE, 'utf8').trim();
    const data = JSON.parse(decryptData(encrypted, getMasterKey()));
    // Migrate: ensure all keys exist
    for (const k of Object.keys(SOCIAL_DEFAULTS)) { if (!data[k]) data[k] = Array.isArray(SOCIAL_DEFAULTS[k]) ? [] : {}; }
    // Migrate old likes -> reactions
    for (const p of data.posts) {
      if (p.likes && !p.reactions) { p.reactions = { like: p.likes }; delete p.likes; }
      if (!p.reactions) p.reactions = {};
      if (!p.media) p.media = [];
      if (!p.visibility) p.visibility = 'public';
    }
    return data;
  } catch { return JSON.parse(JSON.stringify(SOCIAL_DEFAULTS)); }
}
function saveSocialData(data) {
  fs.writeFileSync(SOCIAL_FILE, encryptData(JSON.stringify(data), getMasterKey()), 'utf8');
}

// ═══════ Approval queue (encrypted) ═══════
function loadApprovals() {
  if (!fs.existsSync(APPROVALS_FILE)) return { items: [] };
  try {
    const encrypted = fs.readFileSync(APPROVALS_FILE, 'utf8').trim();
    return JSON.parse(decryptData(encrypted, getMasterKey()));
  } catch { return { items: [] }; }
}
function saveApprovals(data) {
  fs.writeFileSync(APPROVALS_FILE, encryptData(JSON.stringify(data), getMasterKey()), 'utf8');
}

// ═══════ Classroom data (encrypted) ═══════
const CLASSROOM_DEFAULTS = { shared: [] };
function loadClassroomData() {
  if (!fs.existsSync(CLASSROOM_FILE)) return JSON.parse(JSON.stringify(CLASSROOM_DEFAULTS));
  try {
    const encrypted = fs.readFileSync(CLASSROOM_FILE, 'utf8').trim();
    const data = JSON.parse(decryptData(encrypted, getMasterKey()));
    if (!Array.isArray(data.shared)) data.shared = [];
    return data;
  } catch { return JSON.parse(JSON.stringify(CLASSROOM_DEFAULTS)); }
}
function saveClassroomData(data) {
  fs.writeFileSync(CLASSROOM_FILE, encryptData(JSON.stringify(data), getMasterKey()), 'utf8');
}

// ═══════ Chat data (encrypted) ═══════
const CHAT_DEFAULTS = { messages: [], reports: [] };
const typingState = {}; // in-memory: { 'user1::user2': { username: 'user1', until: Date.now()+3000 } }
function loadChatData() {
  if (!fs.existsSync(CHAT_FILE)) return JSON.parse(JSON.stringify(CHAT_DEFAULTS));
  try {
    const encrypted = fs.readFileSync(CHAT_FILE, 'utf8').trim();
    const data = JSON.parse(decryptData(encrypted, getMasterKey()));
    if (!Array.isArray(data.messages)) data.messages = [];
    if (!Array.isArray(data.reports)) data.reports = [];
    return data;
  } catch { return JSON.parse(JSON.stringify(CHAT_DEFAULTS)); }
}
function saveChatData(data) {
  fs.writeFileSync(CHAT_FILE, encryptData(JSON.stringify(data), getMasterKey()), 'utf8');
}

// ═══════ User profile helpers ═══════
function getUserProfile(username) {
  const users = loadUsers();
  const u = users[username];
  if (!u) return null;
  return {
    username, displayName: u.displayName || username,
    handle: u.handle || '@' + username.replace(/[^a-z0-9_]/g, ''),
    avatar: u.avatarFile ? `/api/avatars/${u.avatarFile}` : null,
    role: u.role || 'user', createdBy: u.createdBy || null, createdAt: u.createdAt
  };
}

function getAdminOf(username) {
  const users = loadUsers();
  const u = users[username];
  return u ? (u.createdBy || null) : null;
}

function normalizeAccountUsername(username) {
  return String(username || '').toLowerCase().trim();
}

function isValidAccountUsername(username) {
  return /^[a-z0-9][a-z0-9._-]{2,31}$/.test(username);
}

function normalizeAccountRole(role) {
  const r = String(role || 'user').toLowerCase().trim();
  if (r === 'slave') return 'student';
  if (['admin', 'student', 'user'].includes(r)) return r;
  return null;
}

function createAccountWithRole({ username, password, role = 'user', createdBy = null, displayName = null, handle = null }) {
  const uid = normalizeAccountUsername(username);
  if (!isValidAccountUsername(uid)) {
    return { success: false, error: 'Invalid username. Use 3-32 chars: a-z, 0-9, dot, underscore, hyphen' };
  }
  if (!password || String(password).length < 4) {
    return { success: false, error: 'Password must be at least 4 characters' };
  }
  const normalizedRole = normalizeAccountRole(role);
  if (!normalizedRole) return { success: false, error: 'Invalid role. Use admin, slave/student, or user' };

  const result = createAccount(uid, String(password));
  if (!result.success) return result;

  const users = loadUsers();
  users[uid].role = normalizedRole;
  users[uid].createdBy = createdBy ? normalizeAccountUsername(createdBy) : null;
  users[uid].displayName = (displayName || uid).substring(0, 50);
  users[uid].handle = (handle || ('@' + uid.replace(/[^a-z0-9_]/g, ''))).substring(0, 50);
  saveUsers(users);
  writeActionLog('account.create', {
    username: uid,
    role: normalizedRole,
    createdBy: users[uid].createdBy || null
  }, createdBy || 'system');

  return { success: true, username: uid, role: normalizedRole, folderHash: result.folderHash };
}

function createAccount(username, password) {
  const users = loadUsers();
  const uid = username.toLowerCase().trim();
  if (users[uid]) return { success: false, error: 'Account already exists' };
  const { hash, salt } = hashPassword(password);
  const folderHash = hashUsername(uid);
  users[uid] = {
    passwordHash: hash,
    salt: salt,
    folderHash: folderHash,
    createdAt: new Date().toISOString(),
    role: 'user'
  };
  saveUsers(users);
  const userDir = path.join(INTERNAL_ROOT, folderHash);
  if (!fs.existsSync(userDir)) fs.mkdirSync(userDir, { recursive: true });
  return { success: true, folderHash };
}

function deleteAccount(username) {
  const users = loadUsers();
  const uid = username.toLowerCase().trim();
  if (!users[uid]) return { success: false, error: 'Account not found' };
  delete users[uid];
  saveUsers(users);
  writeActionLog('account.delete', { username: uid }, 'system');
  return { success: true };
}

function listAccounts() {
  const users = loadUsers();
  return Object.keys(users).map(uid => ({
    username: uid,
    folderHash: users[uid].folderHash,
    createdAt: users[uid].createdAt,
    role: users[uid].role || 'user'
  }));
}

function authenticateUser(username, password) {
  const users = loadUsers();
  const uid = username.toLowerCase().trim();
  const user = users[uid];
  if (!user) return null;
  if (!verifyPassword(password, user.passwordHash, user.salt)) return null;
  return { username: uid, folderHash: user.folderHash, role: user.role || 'user' };
}

// ═══════ Session management (in-memory) ═══════
const sessions = new Map();
const SESSION_TTL = 24 * 60 * 60 * 1000; // 24h

function createSession(userInfo) {
  const token = crypto.randomBytes(48).toString('hex');
  sessions.set(token, { ...userInfo, createdAt: Date.now() });
  return token;
}

function validateSession(token) {
  if (!token) return null;
  const session = sessions.get(token);
  if (!session) return null;
  if (Date.now() - session.createdAt > SESSION_TTL) {
    sessions.delete(token);
    return null;
  }
  return session;
}

function destroySession(token) { sessions.delete(token); }

// Cleanup expired sessions periodically
setInterval(() => {
  const now = Date.now();
  for (const [token, session] of sessions) {
    if (now - session.createdAt > SESSION_TTL) sessions.delete(token);
  }
}, 60 * 60 * 1000);

// ═══════ Sole-account admin enforcement ═══════
// If exactly one account exists, force it to admin regardless of its current role.
function enforceSoleAccountAdmin() {
  const users = loadUsers();
  const uids = Object.keys(users);
  if (uids.length !== 1) return;
  const uid = uids[0];
  const currentRole = users[uid].role || 'user';
  if (currentRole === 'admin') return; // already admin
  users[uid].role = 'admin';
  saveUsers(users);
  // Also update any active session for this user
  for (const [, session] of sessions) {
    if (session.username === uid) session.role = 'admin';
  }
  logInfo(`Sole account "${uid}" promoted to admin (was "${currentRole}")`);
  writeActionLog('account.auto-promote', { username: uid, previousRole: currentRole, reason: 'sole_account' }, 'system');
}

// Run on startup and check every 30 seconds
enforceSoleAccountAdmin();
setInterval(enforceSoleAccountAdmin, 30 * 1000);

// ═══════ Initialize storage ═══════
if (!fs.existsSync(INTERNAL_ROOT)) fs.mkdirSync(INTERNAL_ROOT, { recursive: true });
if (!fs.existsSync(CONVERT_TEMP_DIR)) fs.mkdirSync(CONVERT_TEMP_DIR, { recursive: true });
if (!fs.existsSync(AVATARS_DIR)) fs.mkdirSync(AVATARS_DIR, { recursive: true });
if (!fs.existsSync(STAGING_DIR)) fs.mkdirSync(STAGING_DIR, { recursive: true });
if (!fs.existsSync(MEDIA_DIR)) fs.mkdirSync(MEDIA_DIR, { recursive: true });
if (!fs.existsSync(CHAT_ATTACHMENTS_DIR)) fs.mkdirSync(CHAT_ATTACHMENTS_DIR, { recursive: true });
getMasterKey();

// Stats tracking
const stats = {
  totalViews: 0,
  totalDownloads: 0,
  startTime: Date.now(),
  fileViews: {}
};

// ═══════ Auth middleware ═══════
function authRequired(req, res, next) {
  const authHeader = req.headers.authorization;
  let token = null;
  if (authHeader && authHeader.startsWith('Bearer ')) {
    token = authHeader.slice(7);
  } else if (req.query.token) {
    token = req.query.token;
  }
  const session = validateSession(token);
  if (!session) {
    return res.status(401).json({ error: 'Authentication required', code: 'AUTH_REQUIRED' });
  }
  req.user = session;
  req.userDir = path.join(INTERNAL_ROOT, session.folderHash);
  if (!fs.existsSync(req.userDir)) fs.mkdirSync(req.userDir, { recursive: true });
  next();
}

function adminRequired(req, res, next) {
  if (req.user.role !== 'admin') return res.status(403).json({ error: 'Admin access required' });
  next();
}

// ═══════ Dynamic multer per user ═══════
function getUserUpload(req) {
  const userDir = req.userDir;
  const userStorage = multer.diskStorage({
    destination: (r, file, cb) => cb(null, userDir),
    filename: (r, file, cb) => {
      const name = Buffer.from(file.originalname, 'latin1').toString('utf8');
      const target = path.join(userDir, name);
      if (fs.existsSync(target)) {
        const ext = path.extname(name);
        const base = path.basename(name, ext);
        cb(null, `${base}_${Date.now()}${ext}`);
      } else {
        cb(null, name);
      }
    }
  });
  return multer({
    storage: userStorage,
    fileFilter: (r, file, cb) => {
      const allowed = ['application/pdf','application/msword',
        'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
        'application/vnd.ms-powerpoint',
        'application/vnd.openxmlformats-officedocument.presentationml.presentation',
        'text/plain','image/png','image/jpeg','image/gif','image/webp',
        'image/svg+xml','image/bmp','image/tiff','image/x-icon','image/avif',
        'image/heic','image/heif'];
      const allowedExts = ['.pdf','.doc','.docx','.ppt','.pptx','.txt',
        '.png','.jpg','.jpeg','.gif','.webp','.svg','.bmp','.tiff','.tif',
        '.ico','.avif','.heic','.heif'];
      const ext = path.extname(file.originalname).toLowerCase();
      if (allowed.includes(file.mimetype) || allowedExts.includes(ext)) cb(null, true);
      else cb(new Error('File type not supported'), false);
    },
    limits: { fileSize: 500 * 1024 * 1024 }
  });
}

app.use(cors());
app.use(express.json());

// ═══════ Mobile auto-detection middleware ═══════
// Automatically serves mobile-optimised HTML when a mobile browser is detected.
// The detection runs server-side via User-Agent so no manual toggle is needed.
const MOBILE_UA_RE = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini|Mobile|mobile|CriOS/i;
const MOBILE_PAGE_MAP = {
  '/':            '/mobile-index.html',
  '/index.html':  '/mobile-index.html',
  '/chat.html':   '/mobile-chat.html',
  '/social.html': '/mobile-social.html',
  '/drive.html':  '/mobile-drive.html',
  '/vm.html':     '/mobile-vm.html',
  '/offers.html': '/mobile-offers.html',
  '/resources.html': '/mobile-resources.html',
};
app.use((req, res, next) => {
  // Skip if the client explicitly opts out (?desktop=1)
  if (req.query.desktop === '1') return next();
  const ua = req.headers['user-agent'] || '';
  const mobilePath = MOBILE_PAGE_MAP[req.path];
  if (mobilePath && MOBILE_UA_RE.test(ua)) {
    const absPath = path.join(__dirname, 'public', mobilePath);
    if (fs.existsSync(absPath)) return res.sendFile(absPath);
  }
  next();
});

app.use(express.static(path.join(__dirname, 'public')));

function isUnsafeName(name) {
  return !name || name.includes('..') || name.includes('/') || name.includes('\\');
}

// ═══════ Office/PDF conversion ═══════
async function convertOfficeFileToPdf(inputPath, sourceName, outputDir, outputPdfName) {
  const ext = path.extname(sourceName).toLowerCase();
  const baseName = path.basename(sourceName, ext).replace(/[^\w.-]/g, '_');
  const uniquePrefix = `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
  const tmpInputName = `${uniquePrefix}${ext}`;
  const tmpOutputName = `${uniquePrefix}.pdf`;
  const tmpInputPath = path.join(CONVERT_TEMP_DIR, tmpInputName);
  const tmpOutputPath = path.join(CONVERT_TEMP_DIR, tmpOutputName);
  const finalPdfName = outputPdfName || `${baseName}_export_${Date.now()}.pdf`;
  const finalPdfPath = path.join(outputDir, finalPdfName);

  await fsp.copyFile(inputPath, tmpInputPath);
  try {
    await execFileAsync('soffice', [
      '--headless','--convert-to','pdf','--outdir',CONVERT_TEMP_DIR,tmpInputPath
    ], { timeout: 120000, windowsHide: true });
    if (!fs.existsSync(tmpOutputPath)) throw new Error('Conversion failed: output PDF was not generated');
    await fsp.copyFile(tmpOutputPath, finalPdfPath);
    fs.unlinkSync(tmpOutputPath);
    return finalPdfName;
  } finally {
    if (fs.existsSync(tmpInputPath)) fs.unlinkSync(tmpInputPath);
    if (fs.existsSync(tmpOutputPath)) fs.unlinkSync(tmpOutputPath);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//  AUTH API
// ════════════════════════════════════════════════════════════════════════════
app.post('/api/auth/login', (req, res) => {
  const { username, password } = req.body;
  if (!username || !password) return res.status(400).json({ error: 'Username and password required' });
  const user = authenticateUser(username, password);
  if (!user) return res.status(401).json({ error: 'Invalid username or password' });
  const token = createSession(user);
  res.json({ success: true, token, username: user.username, role: user.role });
});

app.post('/api/auth/logout', (req, res) => {
  const authHeader = req.headers.authorization;
  if (authHeader && authHeader.startsWith('Bearer ')) destroySession(authHeader.slice(7));
  res.json({ success: true });
});

app.get('/api/auth/verify', (req, res) => {
  const authHeader = req.headers.authorization;
  let token = authHeader && authHeader.startsWith('Bearer ') ? authHeader.slice(7) : null;
  const session = validateSession(token);
  if (!session) return res.status(401).json({ valid: false });
  res.json({ valid: true, username: session.username, role: session.role });
});

// ════════════════════════════════════════════════════════════════════════════
//  PROTECTED APIs (require auth)
// ════════════════════════════════════════════════════════════════════════════

app.get('/api/pdfs', authRequired, (req, res) => {
  fs.readdir(req.userDir, (err, files) => {
    if (err) return res.status(500).json({ error: 'Failed to read documents folder' });
    const supportedExts = ['.pdf','.doc','.docx','.ppt','.pptx','.txt','.png','.jpg','.jpeg','.gif','.webp','.svg','.bmp','.tiff','.tif','.ico','.avif','.heic','.heif'];
    const docs = files
      .filter(file => !file.startsWith('.') && supportedExts.some(ext => file.toLowerCase().endsWith(ext)))
      .map(file => {
        const stats_f = fs.statSync(path.join(req.userDir, file));
        const ext = path.extname(file).toLowerCase();
        return {
          name: file, size: stats_f.size, modified: stats_f.mtime,
          created: stats_f.birthtime, type: ext.replace('.', ''),
          views: stats.fileViews[`${req.user.folderHash}:${file}`] || 0
        };
      })
      .sort((a, b) => a.name.localeCompare(b.name));
    res.json(docs);
  });
});

app.get('/api/search', authRequired, (req, res) => {
  const query = (req.query.q || '').toLowerCase();
  if (!query) return res.json([]);
  fs.readdir(req.userDir, (err, files) => {
    if (err) return res.status(500).json({ error: 'Search failed' });
    const results = files
      .filter(file => !file.startsWith('.') && file.toLowerCase().includes(query))
      .map(file => {
        const s = fs.statSync(path.join(req.userDir, file));
        return { name: file, size: s.size, modified: s.mtime, type: path.extname(file).replace('.', '') };
      });
    res.json(results);
  });
});

app.get('/api/stats', authRequired, (req, res) => {
  const supportedExts = ['.pdf','.doc','.docx','.ppt','.pptx','.txt','.png','.jpg','.jpeg','.gif','.webp','.svg','.bmp','.tiff','.tif','.ico','.avif','.heic','.heif'];
  let allFiles = [];
  try { allFiles = fs.readdirSync(req.userDir).filter(f => !f.startsWith('.') && supportedExts.some(e => f.toLowerCase().endsWith(e))); } catch {}
  const totalFiles = allFiles.length;
  const totalSize = allFiles.reduce((sum, f) => { try { return sum + fs.statSync(path.join(req.userDir, f)).size; } catch { return sum; } }, 0);
  const pdfCount = allFiles.filter(f => f.toLowerCase().endsWith('.pdf')).length;
  const imgCount = allFiles.filter(f => ['.png','.jpg','.jpeg','.gif','.webp','.svg','.bmp','.tiff','.tif','.ico','.avif','.heic','.heif'].some(e => f.toLowerCase().endsWith(e))).length;
  const docCount = allFiles.filter(f => ['.doc','.docx','.txt'].some(e => f.toLowerCase().endsWith(e))).length;
  const pptCount = allFiles.filter(f => ['.ppt','.pptx'].some(e => f.toLowerCase().endsWith(e))).length;
  res.json({
    totalFiles, totalSize, pdfCount, imgCount, docCount, pptCount,
    totalViews: stats.totalViews, totalDownloads: stats.totalDownloads,
    uptime: Date.now() - stats.startTime
  });
});

app.post('/api/convert/docx-to-pdf/:filename', authRequired, async (req, res) => {
  const filename = req.params.filename;
  if (isUnsafeName(filename)) return res.status(400).json({ error: 'Invalid filename' });
  const inputPath = path.join(req.userDir, filename);
  if (!fs.existsSync(inputPath)) return res.status(404).json({ error: 'File not found' });
  const ext = path.extname(filename).toLowerCase();
  if (!['.docx','.doc'].includes(ext)) return res.status(400).json({ error: 'Only DOC/DOCX supported' });
  try {
    const pdfName = await convertOfficeFileToPdf(inputPath, filename, req.userDir);
    return res.json({
      success: true, pdfName,
      viewUrl: `/documents/${encodeURIComponent(pdfName)}`,
      downloadUrl: `/api/download/${encodeURIComponent(pdfName)}`
    });
  } catch (error) {
    if (error.code === 'ENOENT') return res.status(500).json({ error: 'LibreOffice (soffice) is not installed on the server' });
    return res.status(500).json({ error: error.message || 'Conversion failed' });
  }
});

app.post('/api/convert/presentation-to-pdf/:filename', authRequired, async (req, res) => {
  const filename = req.params.filename;
  if (isUnsafeName(filename)) return res.status(400).json({ error: 'Invalid filename' });
  const inputPath = path.join(req.userDir, filename);
  if (!fs.existsSync(inputPath)) return res.status(404).json({ error: 'File not found' });
  const ext = path.extname(filename).toLowerCase();
  if (!['.pptx','.ppt'].includes(ext)) return res.status(400).json({ error: 'Only PPT/PPTX supported' });
  try {
    const baseName = path.basename(filename, ext).replace(/[^\w.-]/g, '_');
    const pdfName = await convertOfficeFileToPdf(inputPath, filename, req.userDir, `${baseName}_preview.pdf`);
    return res.json({ success: true, pdfName, viewUrl: `/documents/${encodeURIComponent(pdfName)}` });
  } catch (error) {
    if (error.code === 'ENOENT') return res.status(500).json({ error: 'LibreOffice (soffice) is not installed on the server' });
    return res.status(500).json({ error: error.message || 'Presentation conversion failed' });
  }
});

app.post('/api/ocr/pdf/:filename', authRequired, async (req, res) => {
  const filename = req.params.filename;
  if (isUnsafeName(filename)) return res.status(400).json({ error: 'Invalid filename' });
  const inputPath = path.join(req.userDir, filename);
  if (!fs.existsSync(inputPath)) return res.status(404).json({ error: 'File not found' });
  if (path.extname(filename).toLowerCase() !== '.pdf') return res.status(400).json({ error: 'OCR is available only for PDF files' });
  const maxPages = Math.max(1, Math.min(25, Number(req.body?.maxPages) || 10));
  const forceOcr = Boolean(req.body?.forceOcr);
  const runId = `${Date.now()}-${Math.random().toString(36).slice(2, 7)}`;
  const txtOutPath = path.join(CONVERT_TEMP_DIR, `${runId}.txt`);
  const imagePrefix = path.join(CONVERT_TEMP_DIR, `${runId}-page`);

  try {
    let extracted = '';
    try {
      await execFileAsync('pdftotext', ['-f','1','-l',String(maxPages),'-layout',inputPath,txtOutPath], { timeout: 120000, windowsHide: true });
      if (fs.existsSync(txtOutPath)) extracted = (await fsp.readFile(txtOutPath, 'utf8')).trim();
    } catch (err) { if (err.code !== 'ENOENT') console.warn('pdftotext failed:', err.message); }
    if (extracted.length > 40 && !forceOcr) {
      return res.json({ success: true, source: 'text-layer', pagesProcessed: maxPages, text: extracted });
    }
    await execFileAsync('pdftoppm', ['-f','1','-l',String(maxPages),'-r','220','-png',inputPath,imagePrefix], { timeout: 180000, windowsHide: true });
    const generated = (await fsp.readdir(CONVERT_TEMP_DIR))
      .filter(name => name.startsWith(`${runId}-page-`) && name.endsWith('.png'))
      .sort((a, b) => a.localeCompare(b, undefined, { numeric: true }));
    if (!generated.length) return res.status(500).json({ error: 'OCR failed: no page images generated' });
    const pageTexts = [];
    for (let i = 0; i < generated.length; i++) {
      const pageImg = path.join(CONVERT_TEMP_DIR, generated[i]);
      const { stdout } = await execFileAsync('tesseract', [pageImg,'stdout','-l','eng','--psm','1'], { timeout: 180000, windowsHide: true, maxBuffer: 20*1024*1024 });
      pageTexts.push(`\n--- Page ${i + 1} ---\n${(stdout||'').trim()}`);
    }
    return res.json({ success: true, source: 'ocr', pagesProcessed: generated.length, text: pageTexts.join('\n').trim() });
  } catch (error) {
    if (error.code === 'ENOENT') return res.status(500).json({ error: 'OCR tools missing. Install poppler-utils and tesseract-ocr' });
    return res.status(500).json({ error: error.message || 'OCR failed' });
  } finally {
    if (fs.existsSync(txtOutPath)) fs.unlinkSync(txtOutPath);
    try {
      const tempFiles = await fsp.readdir(CONVERT_TEMP_DIR);
      for (const name of tempFiles) {
        if (name.startsWith(`${runId}-page-`) && name.endsWith('.png')) fs.unlinkSync(path.join(CONVERT_TEMP_DIR, name));
      }
    } catch {}
  }
});

app.put('/api/rename', authRequired, (req, res) => {
  const { oldName, newName } = req.body;
  if (!oldName || !newName) return res.status(400).json({ error: 'Both oldName and newName required' });
  if (oldName.includes('..') || newName.includes('..')) return res.status(400).json({ error: 'Invalid filename' });
  const oldPath = path.join(req.userDir, oldName);
  const newPath = path.join(req.userDir, newName);
  if (!fs.existsSync(oldPath)) return res.status(404).json({ error: 'File not found' });
  if (fs.existsSync(newPath)) return res.status(409).json({ error: 'A file with that name already exists' });
  fs.renameSync(oldPath, newPath);
  res.json({ success: true, name: newName });
});

app.post('/api/bulk-download', authRequired, (req, res) => {
  const { files } = req.body;
  if (!files || !files.length) return res.status(400).json({ error: 'No files specified' });
  res.setHeader('Content-Type', 'application/zip');
  res.setHeader('Content-Disposition', 'attachment; filename="prenxy-documents.zip"');
  const archive = archiver('zip', { zlib: { level: 5 } });
  archive.on('error', err => res.status(500).json({ error: err.message }));
  archive.pipe(res);
  for (const file of files) {
    if (file.includes('..') || file.includes('/') || file.includes('\\')) continue;
    const filePath = path.join(req.userDir, file);
    if (fs.existsSync(filePath)) { archive.file(filePath, { name: file }); stats.totalDownloads++; }
  }
  archive.finalize();
});

app.get('/documents/:filename', authRequired, (req, res) => {
  const filename = req.params.filename;
  if (filename.includes('..') || filename.includes('/') || filename.includes('\\'))
    return res.status(400).json({ error: 'Invalid filename' });
  const filePath = path.join(req.userDir, filename);
  if (!fs.existsSync(filePath)) return res.status(404).json({ error: 'File not found' });
  stats.totalViews++;
  const viewKey = `${req.user.folderHash}:${filename}`;
  stats.fileViews[viewKey] = (stats.fileViews[viewKey] || 0) + 1;
  const ext = path.extname(filename).toLowerCase();
  const mimeTypes = {
    '.pdf':'application/pdf','.doc':'application/msword',
    '.docx':'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
    '.ppt':'application/vnd.ms-powerpoint',
    '.pptx':'application/vnd.openxmlformats-officedocument.presentationml.presentation',
    '.txt':'text/plain','.png':'image/png','.jpg':'image/jpeg','.jpeg':'image/jpeg',
    '.gif':'image/gif','.webp':'image/webp','.svg':'image/svg+xml','.bmp':'image/bmp',
    '.tiff':'image/tiff','.tif':'image/tiff','.ico':'image/x-icon',
    '.avif':'image/avif','.heic':'image/heic','.heif':'image/heif'
  };
  res.setHeader('Content-Type', mimeTypes[ext] || 'application/octet-stream');
  res.setHeader('Content-Disposition', `inline; filename="${filename}"`);
  res.sendFile(filePath);
});

app.get('/api/download/:filename', authRequired, (req, res) => {
  const filename = req.params.filename;
  if (filename.includes('..') || filename.includes('/') || filename.includes('\\'))
    return res.status(400).json({ error: 'Invalid filename' });
  const filePath = path.join(req.userDir, filename);
  if (!fs.existsSync(filePath)) return res.status(404).json({ error: 'File not found' });
  stats.totalDownloads++;
  const stat = fs.statSync(filePath);
  res.setHeader('Content-Type', 'application/octet-stream');
  res.setHeader('Content-Disposition', `attachment; filename="${filename}"`);
  res.setHeader('Content-Length', stat.size);
  fs.createReadStream(filePath).pipe(res);
});

app.post('/api/upload', authRequired, (req, res, next) => {
  const isStudent = req.user.role === 'student';
  // Students upload to staging dir for approval
  const targetDir = isStudent ? STAGING_DIR : req.userDir;
  const origUserDir = req.userDir;
  if (isStudent) req.userDir = STAGING_DIR;
  const upload = getUserUpload(req);
  req.userDir = origUserDir; // restore
  upload.array('files', 50)(req, res, (err) => {
    if (err) {
      if (err instanceof multer.MulterError) return res.status(400).json({ error: err.message });
      return res.status(400).json({ error: err.message });
    }
    if (!req.files || req.files.length === 0) return res.status(400).json({ error: 'No files uploaded' });
    const uploaded = req.files.map(f => ({
      name: f.filename, size: f.size, modified: new Date(), type: path.extname(f.filename).replace('.', '')
    }));
    if (isStudent) {
      const approvals = loadApprovals();
      for (const f of req.files) {
        approvals.items.push({
          id: crypto.randomBytes(16).toString('hex'),
          type: 'upload', requestedBy: req.user.username,
          adminUser: getAdminOf(req.user.username),
          filename: f.filename, stagingPath: path.join(STAGING_DIR, f.filename),
          targetDir: origUserDir, status: 'pending',
          timestamp: new Date().toISOString()
        });
      }
      saveApprovals(approvals);
      return res.json({ success: true, files: uploaded, pendingApproval: true });
    }
    res.json({ success: true, files: uploaded });
  });
});

app.delete('/api/pdfs/:filename', authRequired, (req, res) => {
  const filename = req.params.filename;
  if (filename.includes('..') || filename.includes('/') || filename.includes('\\'))
    return res.status(400).json({ error: 'Invalid filename' });
  const filePath = path.join(req.userDir, filename);
  if (!fs.existsSync(filePath)) return res.status(404).json({ error: 'File not found' });
  if (req.user.role === 'student') {
    const approvals = loadApprovals();
    approvals.items.push({
      id: crypto.randomBytes(16).toString('hex'),
      type: 'delete', requestedBy: req.user.username,
      adminUser: getAdminOf(req.user.username),
      filename, filePath, status: 'pending',
      timestamp: new Date().toISOString()
    });
    saveApprovals(approvals);
    return res.json({ success: true, pendingApproval: true });
  }
  fs.unlinkSync(filePath);
  res.json({ success: true });
});

app.post('/api/bulk-delete', authRequired, (req, res) => {
  const { files } = req.body;
  if (!files || !files.length) return res.status(400).json({ error: 'No files specified' });
  const isStudent = req.user.role === 'student';
  const results = [];
  if (isStudent) {
    const approvals = loadApprovals();
    for (const file of files) {
      if (file.includes('..') || file.includes('/') || file.includes('\\')) continue;
      const filePath = path.join(req.userDir, file);
      if (fs.existsSync(filePath)) {
        approvals.items.push({
          id: crypto.randomBytes(16).toString('hex'),
          type: 'delete', requestedBy: req.user.username,
          adminUser: getAdminOf(req.user.username),
          filename: file, filePath, status: 'pending',
          timestamp: new Date().toISOString()
        });
        results.push({ name: file, pendingApproval: true });
      }
    }
    saveApprovals(approvals);
    return res.json({ success: true, results, pendingApproval: true });
  }
  for (const file of files) {
    if (file.includes('..') || file.includes('/') || file.includes('\\')) continue;
    const filePath = path.join(req.userDir, file);
    if (fs.existsSync(filePath)) { fs.unlinkSync(filePath); results.push({ name: file, deleted: true }); }
  }
  res.json({ success: true, results });
});

// ════════════════════════════════════════════════════════════════════════════
//  PROFILE APIs
// ════════════════════════════════════════════════════════════════════════════
app.get('/api/profile', authRequired, (req, res) => {
  const profile = getUserProfile(req.user.username);
  if (!profile) return res.status(404).json({ error: 'User not found' });
  res.json(profile);
});

app.get('/api/users/:username/profile', authRequired, (req, res) => {
  const profile = getUserProfile(req.params.username.toLowerCase().trim());
  if (!profile) return res.status(404).json({ error: 'User not found' });
  res.json(profile);
});

app.put('/api/profile', authRequired, (req, res) => {
  const { displayName, handle } = req.body;
  const users = loadUsers();
  const uid = req.user.username;
  if (!users[uid]) return res.status(404).json({ error: 'User not found' });
  if (displayName) users[uid].displayName = displayName.substring(0, 50);
  if (handle) {
    const h = handle.startsWith('@') ? handle.substring(0, 30) : ('@' + handle).substring(0, 30);
    const hLower = h.toLowerCase();
    for (const [u, data] of Object.entries(users)) {
      if (u !== uid && data.handle && data.handle.toLowerCase() === hLower)
        return res.status(409).json({ error: 'Handle already taken' });
    }
    users[uid].handle = h;
  }
  saveUsers(users);
  res.json({ success: true });
});

const avatarUpload = multer({
  storage: multer.diskStorage({
    destination: (r, f, cb) => cb(null, AVATARS_DIR),
    filename: (r, f, cb) => {
      const ext = path.extname(f.originalname).toLowerCase() || '.png';
      cb(null, r.user.username.replace(/[^a-z0-9_-]/g, '') + '_' + Date.now() + ext);
    }
  }),
  limits: { fileSize: 5 * 1024 * 1024 },
  fileFilter: (r, f, cb) => {
    const ok = ['image/png', 'image/jpeg', 'image/gif', 'image/webp'].includes(f.mimetype);
    cb(ok ? null : new Error('Only images allowed'), ok);
  }
});

app.post('/api/profile/avatar', authRequired, avatarUpload.single('avatar'), (req, res) => {
  if (!req.file) return res.status(400).json({ error: 'No file uploaded' });
  const users = loadUsers();
  const uid = req.user.username;
  // Delete old avatar
  if (users[uid].avatarFile) {
    const old = path.join(AVATARS_DIR, users[uid].avatarFile);
    if (fs.existsSync(old)) try { fs.unlinkSync(old); } catch {}
  }
  users[uid].avatarFile = req.file.filename;
  saveUsers(users);
  res.json({ success: true, avatar: `/api/avatars/${req.file.filename}` });
});

app.get('/api/avatars/:filename', (req, res) => {
  const filename = req.params.filename;
  if (filename.includes('..') || filename.includes('/')) return res.status(400).end();
  const filePath = path.join(AVATARS_DIR, filename);
  if (!fs.existsSync(filePath)) return res.status(404).end();
  const ext = path.extname(filename).toLowerCase();
  const mime = { '.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.gif': 'image/gif', '.webp': 'image/webp' };
  res.setHeader('Content-Type', mime[ext] || 'image/png');
  res.setHeader('Cache-Control', 'public, max-age=86400');
  res.sendFile(filePath);
});

// ════════════════════════════════════════════════════════════════════════════
//  ADMIN APIs
// ════════════════════════════════════════════════════════════════════════════
function splitCommandLine(input) {
  const out = [];
  const re = /"([^"\\]*(?:\\.[^"\\]*)*)"|'([^'\\]*(?:\\.[^'\\]*)*)'|(\S+)/g;
  const line = String(input || '').trim();
  let m;
  while ((m = re.exec(line)) !== null) out.push((m[1] || m[2] || m[3] || '').replace(/\\(["'])/g, '$1'));
  return out;
}

function maskSensitiveCommand(input) {
  const parts = splitCommandLine(input);
  const cmd = (parts[0] || '').toLowerCase();
  const masked = [...parts];
  const maskAt = (idx) => { if (masked[idx]) masked[idx] = '***'; };
  if (['create-account', 'create-admin', 'create-user', 'reset-password'].includes(cmd)) maskAt(2);
  if (['create-slave', 'create-student'].includes(cmd)) maskAt(3);
  return masked.join(' ');
}

function canManageAccount(actorUsername, actorRole, targetUsername, users) {
  if (!users[targetUsername]) return false;
  if (targetUsername === actorUsername) return false;
  if (actorRole !== 'admin') return false;
  const target = users[targetUsername];
  const targetRole = target.role || 'user';
  if (targetRole === 'admin') return target.createdBy === actorUsername;
  return target.createdBy === actorUsername;
}

function runSafeAdminCommand(actor, commandLine) {
  const users = loadUsers();
  const parts = splitCommandLine(commandLine);
  const cmd = (parts[0] || '').toLowerCase();
  const actorUsername = normalizeAccountUsername(actor.username || '');
  const actorRole = actor.role || 'user';
  const isCli = actor.source === 'cli';
  const isAdminActor = isCli || actorRole === 'admin';

  if (!cmd) return { success: true, output: '' };

  if (cmd === 'help') {
    return {
      success: true,
      output: [
        'Safe commands:',
        '  help',
        '  whoami',
        '  list-accounts [mine|all]',
        '  list-slaves [adminUsername]',
        '  create-admin <username> <password>',
        '  create-slave <adminUsername> <username> <password>',
        '  create-user <username> <password>',
        '  set-role <username> <admin|slave|student|user> [adminUsernameForSlave]',
        '  reset-password <username> <new-password>',
        '  delete-account <username>',
        '  show-logs [count]'
      ].join('\n')
    };
  }

  if (cmd === 'whoami') {
    return { success: true, output: `username=${actorUsername || 'cli'} role=${isCli ? 'root-cli' : actorRole}` };
  }

  if (!isAdminActor) return { success: false, output: 'Only admins can run management commands.' };

  if (cmd === 'list-accounts') {
    const scope = (parts[1] || 'mine').toLowerCase();
    const rows = Object.entries(users)
      .filter(([u, data]) => isCli || scope === 'all' || data.createdBy === actorUsername || u === actorUsername)
      .map(([u, data]) => ({
        username: u,
        role: data.role || 'user',
        createdBy: data.createdBy || '-',
        createdAt: (data.createdAt || '').slice(0, 19)
      }))
      .sort((a, b) => a.username.localeCompare(b.username));
    if (rows.length === 0) return { success: true, output: 'No accounts found.' };
    return {
      success: true,
      output: rows.map(r => `${r.username}\trole=${r.role}\tcreatedBy=${r.createdBy}\tcreatedAt=${r.createdAt}`).join('\n'),
      data: rows
    };
  }

  if (cmd === 'list-slaves') {
    const adminUser = normalizeAccountUsername(parts[1] || actorUsername);
    const rows = Object.entries(users)
      .filter(([, data]) => (data.role || 'user') === 'student' && data.createdBy === adminUser)
      .map(([u, data]) => ({ username: u, createdAt: data.createdAt || null }))
      .sort((a, b) => a.username.localeCompare(b.username));
    return { success: true, output: rows.length ? rows.map(r => `${r.username}\tcreatedAt=${(r.createdAt || '').slice(0, 19)}`).join('\n') : 'No slave/student accounts found.', data: rows };
  }

  if (cmd === 'create-admin') {
    if (parts.length < 3) return { success: false, output: 'Usage: create-admin <username> <password>' };
    const createdBy = isCli ? null : actorUsername;
    const result = createAccountWithRole({ username: parts[1], password: parts[2], role: 'admin', createdBy });
    return result.success
      ? { success: true, output: `Created admin account: ${result.username}`, data: result }
      : { success: false, output: result.error };
  }

  if (cmd === 'create-slave' || cmd === 'create-student') {
    if (parts.length < 4) return { success: false, output: 'Usage: create-slave <adminUsername> <username> <password>' };
    const parentAdmin = normalizeAccountUsername(parts[1]);
    const parent = users[parentAdmin];
    if (!parent || (parent.role || 'user') !== 'admin') return { success: false, output: `Admin not found: ${parentAdmin}` };
    const result = createAccountWithRole({ username: parts[2], password: parts[3], role: 'student', createdBy: parentAdmin });
    return result.success
      ? { success: true, output: `Created slave/student account: ${result.username} under ${parentAdmin}`, data: result }
      : { success: false, output: result.error };
  }

  if (cmd === 'create-user') {
    if (parts.length < 3) return { success: false, output: 'Usage: create-user <username> <password>' };
    const result = createAccountWithRole({ username: parts[1], password: parts[2], role: 'user', createdBy: isCli ? null : actorUsername });
    return result.success
      ? { success: true, output: `Created user account: ${result.username}`, data: result }
      : { success: false, output: result.error };
  }

  if (cmd === 'set-role') {
    if (parts.length < 3) return { success: false, output: 'Usage: set-role <username> <admin|slave|student|user> [adminUsernameForSlave]' };
    const target = normalizeAccountUsername(parts[1]);
    const role = normalizeAccountRole(parts[2]);
    if (!role) return { success: false, output: 'Invalid role.' };
    if (!users[target]) return { success: false, output: `Account not found: ${target}` };
    if (!isCli && !canManageAccount(actorUsername, actorRole, target, users)) return { success: false, output: 'You cannot manage that account.' };
    users[target].role = role;
    if (role === 'student') {
      const adminOwner = normalizeAccountUsername(parts[3] || users[target].createdBy || actorUsername);
      if (!users[adminOwner] || (users[adminOwner].role || 'user') !== 'admin') return { success: false, output: 'A valid admin owner is required for slave/student role.' };
      users[target].createdBy = adminOwner;
    }
    saveUsers(users);
    writeActionLog('account.set-role', { username: target, role, createdBy: users[target].createdBy || null }, actorUsername || 'cli');
    return { success: true, output: `Role for ${target} set to ${role}` };
  }

  if (cmd === 'reset-password') {
    if (parts.length < 3) return { success: false, output: 'Usage: reset-password <username> <new-password>' };
    const target = normalizeAccountUsername(parts[1]);
    if (!users[target]) return { success: false, output: `Account not found: ${target}` };
    if (!isCli && !canManageAccount(actorUsername, actorRole, target, users)) return { success: false, output: 'You cannot manage that account.' };
    if (!parts[2] || parts[2].length < 4) return { success: false, output: 'New password must be at least 4 characters.' };
    const { hash, salt } = hashPassword(parts[2]);
    users[target].passwordHash = hash;
    users[target].salt = salt;
    saveUsers(users);
    writeActionLog('account.reset-password', { username: target }, actorUsername || 'cli');
    return { success: true, output: `Password reset for: ${target}` };
  }

  if (cmd === 'delete-account') {
    if (parts.length < 2) return { success: false, output: 'Usage: delete-account <username>' };
    const target = normalizeAccountUsername(parts[1]);
    if (!users[target]) return { success: false, output: `Account not found: ${target}` };
    if (!isCli && !canManageAccount(actorUsername, actorRole, target, users)) return { success: false, output: 'You cannot manage that account.' };
    delete users[target];
    saveUsers(users);
    writeActionLog('account.delete', { username: target, via: 'safe-command' }, actorUsername || 'cli');
    return { success: true, output: `Deleted account: ${target}` };
  }

  if (cmd === 'show-logs') {
    const count = Math.max(1, Math.min(parseInt(parts[1], 10) || 20, 200));
    const logs = readActionLogs(count);
    if (!logs.length) return { success: true, output: 'No action logs yet.' };
    const out = logs.map(l => {
      const d = l.details && typeof l.details === 'object' ? JSON.stringify(l.details) : '{}';
      return `${l.timestamp}\t${l.actor}\t${l.action}\t${d}`;
    }).join('\n');
    return { success: true, output: out, data: logs };
  }

  return { success: false, output: `Unknown safe command: ${cmd}. Type "help".` };
}

const adminSandboxSessions = new Map(); // username -> { cwdRel: '/', history: [] }

function sanitizeBaseName(name) {
  return String(name || '').replace(/[<>:"|?*]/g, '').trim();
}

function safeResolveSandboxPath(rootDir, cwdRel, inputPath = '.') {
  const raw = String(inputPath || '.').trim();
  const joined = raw.startsWith('/') ? raw : path.posix.join(cwdRel || '/', raw);
  const normalizedRel = path.posix.normalize('/' + joined).replace(/^\/+/, '/');
  const absolute = path.resolve(rootDir, '.' + normalizedRel);
  const normalizedRoot = path.resolve(rootDir);
  if (!(absolute === normalizedRoot || absolute.startsWith(normalizedRoot + path.sep))) {
    throw new Error('Path escapes sandbox root');
  }
  return { absolute, rel: normalizedRel };
}

function ensureAdminSandboxSession(user) {
  const key = user.username;
  if (!adminSandboxSessions.has(key)) adminSandboxSessions.set(key, { cwdRel: '/', history: [] });
  return adminSandboxSessions.get(key);
}

function runAdminSandboxCommand(reqUser, commandLine) {
  const parts = splitCommandLine(commandLine);
  const cmd = (parts[0] || '').toLowerCase();
  const users = loadUsers();
  const me = users[reqUser.username];
  if (!me) return { success: false, output: 'User not found.' };
  const rootDir = path.join(INTERNAL_ROOT, me.folderHash);
  if (!fs.existsSync(rootDir)) fs.mkdirSync(rootDir, { recursive: true });

  const session = ensureAdminSandboxSession(reqUser);
  let cwdRel = session.cwdRel || '/';
  if (!cmd) return { success: true, output: '', cwd: cwdRel };
  session.history = Array.isArray(session.history) ? session.history : [];
  session.history.push({
    ts: new Date().toISOString(),
    command: String(commandLine || '').trim()
  });
  if (session.history.length > 200) session.history = session.history.slice(-200);

  const getTarget = (p) => safeResolveSandboxPath(rootDir, cwdRel, p || '.');
  const readTextFile = (absolutePath) => fs.readFileSync(absolutePath, 'utf8');
  const limitItems = (arr, max = 400) => arr.slice(0, max);

  if (cmd === 'help') {
    return {
      success: true,
      cwd: cwdRel,
      output: [
        'Sandbox commands:',
        '  help, pwd, clear',
        '  history [count]',
        '  ls [path], cd <path>',
        '  tree [path] [depth], du [path]',
        '  cat <file>, head <file> [lines], tail <file> [lines]',
        '  wc <file>, stat <path>',
        '  grep <file> <text>, findname [path] <query>',
        '  touch <file>, mkdir <dir>',
        '  write <file> <text>',
        '  append <file> <text>',
        '  rm <path>, mv <src> <dest>, cp <src> <dest>'
      ].join('\n')
    };
  }

  if (cmd === 'pwd') return { success: true, cwd: cwdRel, output: cwdRel };
  if (cmd === 'clear') return { success: true, cwd: cwdRel, output: '__CLEAR__' };
  if (cmd === 'history') {
    const n = Math.max(1, Math.min(parseInt(parts[1], 10) || 20, 200));
    const rows = session.history.slice(-n);
    if (!rows.length) return { success: true, cwd: cwdRel, output: '(no history)' };
    return { success: true, cwd: cwdRel, output: rows.map((r, idx) => `${idx + 1}. ${r.command}`).join('\n') };
  }

  if (cmd === 'cd') {
    const target = getTarget(parts[1] || '/');
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'No such directory' };
    if (!fs.statSync(target.absolute).isDirectory()) return { success: false, cwd: cwdRel, output: 'Not a directory' };
    session.cwdRel = target.rel;
    return { success: true, cwd: session.cwdRel, output: session.cwdRel };
  }

  if (cmd === 'ls') {
    const target = getTarget(parts[1] || '.');
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'Path not found' };
    const st = fs.statSync(target.absolute);
    if (st.isFile()) return { success: true, cwd: cwdRel, output: sanitizeBaseName(path.basename(target.absolute)) };
    const entries = fs.readdirSync(target.absolute, { withFileTypes: true })
      .sort((a, b) => Number(b.isDirectory()) - Number(a.isDirectory()) || a.name.localeCompare(b.name))
      .map(e => `${e.isDirectory() ? '[DIR] ' : '      '}${sanitizeBaseName(e.name)}`);
    return { success: true, cwd: cwdRel, output: entries.length ? entries.join('\n') : '(empty)' };
  }

  if (cmd === 'cat' || cmd === 'head') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: `Usage: ${cmd} <file>${cmd === 'head' ? ' [lines]' : ''}` };
    const target = getTarget(parts[1]);
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'File not found' };
    if (!fs.statSync(target.absolute).isFile()) return { success: false, cwd: cwdRel, output: 'Not a file' };
    const content = readTextFile(target.absolute);
    if (cmd === 'head') {
      const n = Math.max(1, Math.min(parseInt(parts[2], 10) || 20, 200));
      return { success: true, cwd: cwdRel, output: content.split('\n').slice(0, n).join('\n') };
    }
    return { success: true, cwd: cwdRel, output: content.slice(0, 20000) };
  }

  if (cmd === 'tail') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: 'Usage: tail <file> [lines]' };
    const target = getTarget(parts[1]);
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'File not found' };
    if (!fs.statSync(target.absolute).isFile()) return { success: false, cwd: cwdRel, output: 'Not a file' };
    const content = readTextFile(target.absolute);
    const n = Math.max(1, Math.min(parseInt(parts[2], 10) || 20, 400));
    const lines = content.split('\n');
    return { success: true, cwd: cwdRel, output: lines.slice(Math.max(0, lines.length - n)).join('\n') };
  }

  if (cmd === 'wc') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: 'Usage: wc <file>' };
    const target = getTarget(parts[1]);
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'File not found' };
    if (!fs.statSync(target.absolute).isFile()) return { success: false, cwd: cwdRel, output: 'Not a file' };
    const content = readTextFile(target.absolute);
    const lines = content === '' ? 0 : content.split('\n').length;
    const words = content.trim() ? content.trim().split(/\s+/).length : 0;
    const bytes = Buffer.byteLength(content, 'utf8');
    return { success: true, cwd: cwdRel, output: `lines=${lines} words=${words} bytes=${bytes}` };
  }

  if (cmd === 'stat') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: 'Usage: stat <path>' };
    const target = getTarget(parts[1]);
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'Path not found' };
    const st = fs.statSync(target.absolute);
    return {
      success: true,
      cwd: cwdRel,
      output: [
        `path=${target.rel}`,
        `type=${st.isDirectory() ? 'directory' : 'file'}`,
        `size=${st.size}`,
        `modified=${st.mtime.toISOString()}`,
        `created=${st.birthtime.toISOString()}`
      ].join('\n')
    };
  }

  if (cmd === 'grep') {
    if (!parts[1] || !parts[2]) return { success: false, cwd: cwdRel, output: 'Usage: grep <file> <text>' };
    const target = getTarget(parts[1]);
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'File not found' };
    if (!fs.statSync(target.absolute).isFile()) return { success: false, cwd: cwdRel, output: 'Not a file' };
    const query = parts.slice(2).join(' ').toLowerCase();
    const lines = readTextFile(target.absolute).split('\n');
    const hits = [];
    for (let i = 0; i < lines.length; i++) {
      if (lines[i].toLowerCase().includes(query)) hits.push(`${i + 1}: ${lines[i]}`);
      if (hits.length >= 200) break;
    }
    return { success: true, cwd: cwdRel, output: hits.length ? hits.join('\n') : '(no matches)' };
  }

  if (cmd === 'findname') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: 'Usage: findname [path] <query>' };
    let basePathArg = '.';
    let query = '';
    if (parts.length === 2) query = parts[1];
    else {
      basePathArg = parts[1];
      query = parts.slice(2).join(' ');
    }
    query = query.toLowerCase();
    if (!query) return { success: false, cwd: cwdRel, output: 'Query is required' };
    const base = getTarget(basePathArg);
    if (!fs.existsSync(base.absolute)) return { success: false, cwd: cwdRel, output: 'Path not found' };
    const out = [];
    const walk = (abs, rel, depth = 0) => {
      if (out.length >= 500 || depth > 8) return;
      const entries = fs.readdirSync(abs, { withFileTypes: true });
      for (const entry of entries) {
        const name = sanitizeBaseName(entry.name);
        const childAbs = path.join(abs, entry.name);
        const childRel = path.posix.join(rel, name).replace(/\\/g, '/');
        if (name.toLowerCase().includes(query)) out.push((entry.isDirectory() ? '[DIR] ' : '      ') + childRel);
        if (entry.isDirectory()) walk(childAbs, childRel, depth + 1);
        if (out.length >= 500) break;
      }
    };
    if (fs.statSync(base.absolute).isDirectory()) walk(base.absolute, base.rel);
    else if (path.basename(base.absolute).toLowerCase().includes(query)) out.push(base.rel);
    return { success: true, cwd: cwdRel, output: out.length ? out.join('\n') : '(no matches)' };
  }

  if (cmd === 'tree') {
    const target = getTarget(parts[1] || '.');
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'Path not found' };
    const depthLimit = Math.max(1, Math.min(parseInt(parts[2], 10) || 3, 8));
    const lines = [];
    if (!fs.statSync(target.absolute).isDirectory()) {
      lines.push(target.rel);
      return { success: true, cwd: cwdRel, output: lines.join('\n') };
    }
    const walk = (abs, rel, depth, prefix) => {
      if (depth > depthLimit || lines.length > 500) return;
      const entries = fs.readdirSync(abs, { withFileTypes: true })
        .sort((a, b) => Number(b.isDirectory()) - Number(a.isDirectory()) || a.name.localeCompare(b.name));
      const limited = limitItems(entries, 120);
      for (let i = 0; i < limited.length; i++) {
        const entry = limited[i];
        const isLast = i === limited.length - 1;
        const marker = isLast ? '└─ ' : '├─ ';
        const name = sanitizeBaseName(entry.name);
        lines.push(prefix + marker + name + (entry.isDirectory() ? '/' : ''));
        if (entry.isDirectory()) {
          walk(path.join(abs, entry.name), path.posix.join(rel, name), depth + 1, prefix + (isLast ? '   ' : '│  '));
        }
      }
    };
    lines.push(target.rel + '/');
    walk(target.absolute, target.rel, 1, '');
    return { success: true, cwd: cwdRel, output: lines.join('\n') };
  }

  if (cmd === 'du') {
    const target = getTarget(parts[1] || '.');
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'Path not found' };
    const calcSize = (abs, depth = 0) => {
      if (depth > 20) return 0;
      const st = fs.statSync(abs);
      if (st.isFile()) return st.size;
      let total = 0;
      const entries = fs.readdirSync(abs, { withFileTypes: true });
      for (const entry of entries) {
        total += calcSize(path.join(abs, entry.name), depth + 1);
      }
      return total;
    };
    if (fs.statSync(target.absolute).isFile()) {
      return { success: true, cwd: cwdRel, output: `${target.rel}\t${calcSize(target.absolute)} bytes` };
    }
    const rows = [];
    const entries = fs.readdirSync(target.absolute, { withFileTypes: true });
    for (const entry of limitItems(entries, 200)) {
      const childAbs = path.join(target.absolute, entry.name);
      const childRel = path.posix.join(target.rel, sanitizeBaseName(entry.name));
      rows.push(`${childRel}${entry.isDirectory() ? '/' : ''}\t${calcSize(childAbs)} bytes`);
    }
    const total = calcSize(target.absolute);
    rows.push(`TOTAL\t${total} bytes`);
    return { success: true, cwd: cwdRel, output: rows.join('\n') };
  }

  if (cmd === 'touch') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: 'Usage: touch <file>' };
    const target = getTarget(parts[1]);
    const parent = path.dirname(target.absolute);
    if (!fs.existsSync(parent)) fs.mkdirSync(parent, { recursive: true });
    if (!fs.existsSync(target.absolute)) fs.writeFileSync(target.absolute, '', 'utf8');
    return { success: true, cwd: cwdRel, output: `Touched ${target.rel}` };
  }

  if (cmd === 'mkdir') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: 'Usage: mkdir <dir>' };
    const target = getTarget(parts[1]);
    fs.mkdirSync(target.absolute, { recursive: true });
    return { success: true, cwd: cwdRel, output: `Created ${target.rel}` };
  }

  if (cmd === 'write' || cmd === 'append') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: `Usage: ${cmd} <file> <text>` };
    const target = getTarget(parts[1]);
    const text = parts.slice(2).join(' ');
    if (!text) return { success: false, cwd: cwdRel, output: 'Text is required' };
    const parent = path.dirname(target.absolute);
    if (!fs.existsSync(parent)) fs.mkdirSync(parent, { recursive: true });
    if (cmd === 'write') fs.writeFileSync(target.absolute, text + '\n', 'utf8');
    else fs.appendFileSync(target.absolute, text + '\n', 'utf8');
    return { success: true, cwd: cwdRel, output: `${cmd === 'write' ? 'Wrote' : 'Appended'} ${target.rel}` };
  }

  if (cmd === 'rm') {
    if (!parts[1]) return { success: false, cwd: cwdRel, output: 'Usage: rm <path>' };
    const target = getTarget(parts[1]);
    if (!fs.existsSync(target.absolute)) return { success: false, cwd: cwdRel, output: 'Path not found' };
    fs.rmSync(target.absolute, { recursive: true, force: true });
    return { success: true, cwd: cwdRel, output: `Removed ${target.rel}` };
  }

  if (cmd === 'mv' || cmd === 'cp') {
    if (!parts[1] || !parts[2]) return { success: false, cwd: cwdRel, output: `Usage: ${cmd} <src> <dest>` };
    const src = getTarget(parts[1]);
    const dest = getTarget(parts[2]);
    if (!fs.existsSync(src.absolute)) return { success: false, cwd: cwdRel, output: 'Source not found' };
    const parent = path.dirname(dest.absolute);
    if (!fs.existsSync(parent)) fs.mkdirSync(parent, { recursive: true });
    if (cmd === 'mv') {
      fs.renameSync(src.absolute, dest.absolute);
    } else {
      const srcStat = fs.statSync(src.absolute);
      if (srcStat.isDirectory()) fs.cpSync(src.absolute, dest.absolute, { recursive: true });
      else fs.copyFileSync(src.absolute, dest.absolute);
    }
    return { success: true, cwd: cwdRel, output: `${cmd === 'mv' ? 'Moved' : 'Copied'} to ${dest.rel}` };
  }

  return { success: false, cwd: cwdRel, output: `Unknown command: ${cmd}. Type "help".` };
}

app.post('/api/admin/create-user', authRequired, adminRequired, (req, res) => {
  const { username, password, displayName } = req.body;
  if (!username || !password) return res.status(400).json({ error: 'Username and password required' });
  const result = createAccountWithRole({
    username, password,
    role: 'student',
    createdBy: req.user.username,
    displayName: displayName || username
  });
  if (!result.success) return res.status(400).json({ error: result.error });
  res.json({ success: true, username: result.username, folderHash: result.folderHash });
});

app.get('/api/admin/accounts', authRequired, adminRequired, (req, res) => {
  const users = loadUsers();
  const scope = String(req.query.scope || 'mine').toLowerCase();
  const list = Object.entries(users)
    .filter(([u, data]) => scope === 'all' || data.createdBy === req.user.username || u === req.user.username)
    .map(([u, data]) => ({
      username: u,
      role: data.role || 'user',
      displayName: data.displayName || u,
      createdBy: data.createdBy || null,
      createdAt: data.createdAt || null
    }))
    .sort((a, b) => a.username.localeCompare(b.username));
  res.json(list);
});

app.post('/api/admin/accounts', authRequired, adminRequired, (req, res) => {
  const { username, password, role, displayName, parentAdmin } = req.body || {};
  if (!username || !password || !role) return res.status(400).json({ error: 'username, password and role are required' });

  const normalizedRole = normalizeAccountRole(role);
  if (!normalizedRole) return res.status(400).json({ error: 'Role must be admin, slave/student, or user' });

  const users = loadUsers();
  let createdBy = req.user.username;
  if (normalizedRole === 'student') {
    const owner = normalizeAccountUsername(parentAdmin || req.user.username);
    const ownerData = users[owner];
    if (!ownerData || (ownerData.role || 'user') !== 'admin') {
      return res.status(400).json({ error: 'parentAdmin must be a valid admin username' });
    }
    createdBy = owner;
  }
  if (normalizedRole === 'admin' || normalizedRole === 'user') {
    createdBy = req.user.username;
  }

  const result = createAccountWithRole({ username, password, role: normalizedRole, createdBy, displayName });
  if (!result.success) return res.status(400).json({ error: result.error });
  res.json({ success: true, account: { username: result.username, role: result.role, createdBy } });
});

app.delete('/api/admin/accounts/:username', authRequired, adminRequired, (req, res) => {
  const target = normalizeAccountUsername(req.params.username);
  const users = loadUsers();
  if (!users[target]) return res.status(404).json({ error: 'User not found' });
  if (!canManageAccount(req.user.username, req.user.role, target, users)) {
    return res.status(403).json({ error: 'You can only delete accounts you created (excluding your own account)' });
  }
  delete users[target];
  saveUsers(users);
  res.json({ success: true });
});

app.post('/api/admin/terminal/execute', authRequired, adminRequired, (req, res) => {
  const command = String((req.body && req.body.command) || '').trim();
  if (!command) return res.status(400).json({ error: 'Command is required' });
  const result = runSafeAdminCommand({ username: req.user.username, role: req.user.role, source: 'web' }, command);
  writeActionLog('admin.terminal.execute', {
    command: maskSensitiveCommand(command),
    success: !!result.success
  }, req.user.username);
  res.status(result.success ? 200 : 400).json(result);
});

app.post('/api/admin/sandbox/execute', authRequired, adminRequired, (req, res) => {
  const command = String((req.body && req.body.command) || '').trim();
  if (!command) return res.status(400).json({ error: 'Command is required' });
  let result;
  try {
    result = runAdminSandboxCommand(req.user, command);
  } catch (e) {
    result = { success: false, output: `Sandbox error: ${e.message}` };
  }
  writeActionLog('admin.sandbox.execute', {
    command: maskSensitiveCommand(command),
    success: !!result.success,
    cwd: result.cwd || null
  }, req.user.username);
  res.status(result.success ? 200 : 400).json(result);
});

app.get('/api/admin/sandbox/file', authRequired, adminRequired, (req, res) => {
  const users = loadUsers();
  const me = users[req.user.username];
  if (!me) return res.status(404).json({ error: 'User not found' });
  const rootDir = path.join(INTERNAL_ROOT, me.folderHash);
  if (!fs.existsSync(rootDir)) fs.mkdirSync(rootDir, { recursive: true });
  const session = ensureAdminSandboxSession(req.user);
  const inputPath = String(req.query.path || '').trim();
  if (!inputPath) return res.status(400).json({ error: 'path is required' });
  let target;
  try {
    target = safeResolveSandboxPath(rootDir, session.cwdRel || '/', inputPath);
  } catch (e) {
    return res.status(400).json({ error: e.message });
  }
  if (!fs.existsSync(target.absolute)) return res.status(404).json({ error: 'File not found' });
  if (!fs.statSync(target.absolute).isFile()) return res.status(400).json({ error: 'Path is not a file' });
  const content = fs.readFileSync(target.absolute, 'utf8');
  res.json({ success: true, path: target.rel, content: content.slice(0, 1024 * 1024) });
});

app.put('/api/admin/sandbox/file', authRequired, adminRequired, (req, res) => {
  const users = loadUsers();
  const me = users[req.user.username];
  if (!me) return res.status(404).json({ error: 'User not found' });
  const rootDir = path.join(INTERNAL_ROOT, me.folderHash);
  if (!fs.existsSync(rootDir)) fs.mkdirSync(rootDir, { recursive: true });
  const session = ensureAdminSandboxSession(req.user);
  const inputPath = String((req.body && req.body.path) || '').trim();
  if (!inputPath) return res.status(400).json({ error: 'path is required' });
  const content = String((req.body && req.body.content) || '');
  if (Buffer.byteLength(content, 'utf8') > 1024 * 1024) {
    return res.status(400).json({ error: 'Editor content too large (max 1 MB)' });
  }
  let target;
  try {
    target = safeResolveSandboxPath(rootDir, session.cwdRel || '/', inputPath);
  } catch (e) {
    return res.status(400).json({ error: e.message });
  }
  const parent = path.dirname(target.absolute);
  if (!fs.existsSync(parent)) fs.mkdirSync(parent, { recursive: true });
  fs.writeFileSync(target.absolute, content, 'utf8');
  writeActionLog('admin.sandbox.file.save', { path: target.rel, bytes: Buffer.byteLength(content, 'utf8') }, req.user.username);
  res.json({ success: true, path: target.rel });
});

app.get('/api/admin/system/status', authRequired, adminRequired, (req, res) => {
  const mem = process.memoryUsage();
  res.json({
    pid: process.pid,
    platform: process.platform,
    nodeVersion: process.version,
    uptimeMs: Date.now() - stats.startTime,
    restartEnabled: WEB_RESTART_ENABLED,
    rssBytes: mem.rss,
    heapTotalBytes: mem.heapTotal,
    heapUsedBytes: mem.heapUsed,
    externalBytes: mem.external
  });
});

app.get('/api/admin/system/logs', authRequired, adminRequired, (req, res) => {
  const count = Math.max(1, Math.min(parseInt(req.query.count, 10) || 30, 200));
  const logs = readActionLogs(count);
  res.json({ success: true, logs });
});

app.post('/api/admin/system/restart', authRequired, adminRequired, (req, res) => {
  if (!WEB_RESTART_ENABLED) {
    return res.status(400).json({
      error: 'Restart disabled. Set ALLOW_WEB_RESTART=true and run under pm2/systemd/docker restart policy.'
    });
  }
  writeActionLog('admin.system.restart', { via: 'web', by: req.user.username }, req.user.username);
  res.json({ success: true, message: 'Restart signal accepted. Server will exit now.' });
  setTimeout(() => {
    process.exit(0);
  }, 250);
});

app.get('/api/admin/users', authRequired, adminRequired, (req, res) => {
  const allUsers = loadUsers();
  const myStudents = Object.entries(allUsers)
    .filter(([, u]) => u.createdBy === req.user.username)
    .map(([uid, u]) => ({
      username: uid, displayName: u.displayName || uid,
      handle: u.handle || '@' + uid, role: u.role,
      avatar: u.avatarFile ? `/api/avatars/${u.avatarFile}` : null,
      createdAt: u.createdAt
    }));
  res.json(myStudents);
});

app.delete('/api/admin/users/:username', authRequired, adminRequired, (req, res) => {
  const target = req.params.username.toLowerCase().trim();
  const users = loadUsers();
  if (!users[target]) return res.status(404).json({ error: 'User not found' });
  if (users[target].createdBy !== req.user.username)
    return res.status(403).json({ error: 'Can only delete your own student accounts' });
  delete users[target];
  saveUsers(users);
  res.json({ success: true });
});

app.get('/api/admin/approvals', authRequired, adminRequired, (req, res) => {
  const approvals = loadApprovals();
  const mine = approvals.items.filter(a => a.adminUser === req.user.username && a.status === 'pending');
  res.json(mine);
});

app.post('/api/admin/approvals/:id/:action', authRequired, adminRequired, (req, res) => {
  const { id, action } = req.params;
  if (!['approve', 'reject'].includes(action))
    return res.status(400).json({ error: 'Action must be approve or reject' });
  const approvals = loadApprovals();
  const item = approvals.items.find(a => a.id === id && a.adminUser === req.user.username);
  if (!item) return res.status(404).json({ error: 'Approval not found' });
  if (item.status !== 'pending') return res.status(400).json({ error: 'Already processed' });

  if (action === 'approve') {
    if (item.type === 'upload') {
      // Move from staging to user directory
      if (fs.existsSync(item.stagingPath) && item.targetDir) {
        const dest = path.join(item.targetDir, item.filename);
        try {
          fs.copyFileSync(item.stagingPath, dest);
          fs.unlinkSync(item.stagingPath);
        } catch (e) { return res.status(500).json({ error: 'Failed to move file: ' + e.message }); }
      }
    } else if (item.type === 'delete') {
      if (item.filePath && fs.existsSync(item.filePath)) {
        try { fs.unlinkSync(item.filePath); } catch {}
      }
    }
    item.status = 'approved';
  } else {
    if (item.type === 'upload' && item.stagingPath && fs.existsSync(item.stagingPath)) {
      try { fs.unlinkSync(item.stagingPath); } catch {}
    }
    item.status = 'rejected';
  }
  item.resolvedAt = new Date().toISOString();
  saveApprovals(approvals);
  res.json({ success: true, status: item.status });
});

// ════════════════════════════════════════════════════════════════════════════
//  CLASSROOM SHARING APIs
// ════════════════════════════════════════════════════════════════════════════

// Admin: share a file to classroom
app.post('/api/admin/classroom/share/:filename', authRequired, adminRequired, (req, res) => {
  const filename = req.params.filename;
  if (filename.includes('..') || filename.includes('/') || filename.includes('\\'))
    return res.status(400).json({ error: 'Invalid filename' });
  const filePath = path.join(req.userDir, filename);
  if (!fs.existsSync(filePath)) return res.status(404).json({ error: 'File not found in your drive' });
  const data = loadClassroomData();
  const existing = data.shared.find(s => s.filename === filename && s.sharedBy === req.user.username);
  if (existing) return res.json({ success: true, message: 'Already shared' });
  data.shared.push({
    filename,
    sharedBy: req.user.username,
    sharedByFolder: req.user.folderHash,
    sharedAt: new Date().toISOString()
  });
  saveClassroomData(data);
  res.json({ success: true, message: 'Sent to classroom' });
});

// Admin: unshare a file from classroom
app.post('/api/admin/classroom/unshare/:filename', authRequired, adminRequired, (req, res) => {
  const filename = req.params.filename;
  const data = loadClassroomData();
  const idx = data.shared.findIndex(s => s.filename === filename && s.sharedBy === req.user.username);
  if (idx === -1) return res.json({ success: true, message: 'Not shared' });
  data.shared.splice(idx, 1);
  saveClassroomData(data);
  res.json({ success: true, message: 'Removed from classroom' });
});

// Admin: list their classroom shares
app.get('/api/admin/classroom', authRequired, adminRequired, (req, res) => {
  const data = loadClassroomData();
  const mine = data.shared.filter(s => s.sharedBy === req.user.username);
  res.json(mine);
});

// Student: list classroom files shared by their admin
app.get('/api/classroom/files', authRequired, (req, res) => {
  const adminUser = getAdminOf(req.user.username);
  // Admins can also see their own classroom to verify
  const targetAdmin = req.user.role === 'admin' ? req.user.username : adminUser;
  if (!targetAdmin) return res.json([]);
  const data = loadClassroomData();
  const shared = data.shared.filter(s => s.sharedBy === targetAdmin);
  const users = loadUsers();
  const adminFolder = users[targetAdmin] ? users[targetAdmin].folderHash : null;
  if (!adminFolder) return res.json([]);
  const adminDir = path.join(INTERNAL_ROOT, adminFolder);
  const files = shared.map(s => {
    const fp = path.join(adminDir, s.filename);
    if (!fs.existsSync(fp)) return null;
    const st = fs.statSync(fp);
    const ext = path.extname(s.filename).toLowerCase().replace('.', '');
    return {
      name: s.filename, size: st.size, modified: st.mtime,
      created: st.birthtime, type: ext,
      sharedBy: targetAdmin, sharedAt: s.sharedAt,
      classroom: true
    };
  }).filter(Boolean);
  res.json(files);
});

// Student: access a classroom document (served from admin's folder)
app.get('/api/classroom/documents/:filename', authRequired, (req, res) => {
  const filename = req.params.filename;
  if (filename.includes('..') || filename.includes('/') || filename.includes('\\'))
    return res.status(400).json({ error: 'Invalid filename' });
  const adminUser = getAdminOf(req.user.username);
  const targetAdmin = req.user.role === 'admin' ? req.user.username : adminUser;
  if (!targetAdmin) return res.status(403).json({ error: 'No classroom access' });
  const data = loadClassroomData();
  const entry = data.shared.find(s => s.filename === filename && s.sharedBy === targetAdmin);
  if (!entry) return res.status(404).json({ error: 'File not shared to classroom' });
  const users = loadUsers();
  const adminFolder = users[targetAdmin] ? users[targetAdmin].folderHash : null;
  if (!adminFolder) return res.status(404).json({ error: 'Admin folder not found' });
  const fp = path.join(INTERNAL_ROOT, adminFolder, filename);
  if (!fs.existsSync(fp)) return res.status(404).json({ error: 'File no longer exists' });
  const ext = path.extname(filename).toLowerCase();
  const mimeTypes = {
    '.pdf':'application/pdf','.doc':'application/msword',
    '.docx':'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
    '.ppt':'application/vnd.ms-powerpoint',
    '.pptx':'application/vnd.openxmlformats-officedocument.presentationml.presentation',
    '.txt':'text/plain','.png':'image/png','.jpg':'image/jpeg','.jpeg':'image/jpeg',
    '.gif':'image/gif','.webp':'image/webp','.svg':'image/svg+xml','.bmp':'image/bmp',
    '.tiff':'image/tiff','.tif':'image/tiff','.ico':'image/x-icon',
    '.avif':'image/avif','.heic':'image/heic','.heif':'image/heif'
  };
  res.setHeader('Content-Type', mimeTypes[ext] || 'application/octet-stream');
  res.setHeader('Content-Disposition', `inline; filename="${filename}"`);
  res.sendFile(fp);
});

// Student: download a classroom document
app.get('/api/classroom/download/:filename', authRequired, (req, res) => {
  const filename = req.params.filename;
  if (filename.includes('..') || filename.includes('/') || filename.includes('\\'))
    return res.status(400).json({ error: 'Invalid filename' });
  const adminUser = getAdminOf(req.user.username);
  const targetAdmin = req.user.role === 'admin' ? req.user.username : adminUser;
  if (!targetAdmin) return res.status(403).json({ error: 'No classroom access' });
  const data = loadClassroomData();
  const entry = data.shared.find(s => s.filename === filename && s.sharedBy === targetAdmin);
  if (!entry) return res.status(404).json({ error: 'File not shared to classroom' });
  const users = loadUsers();
  const adminFolder = users[targetAdmin] ? users[targetAdmin].folderHash : null;
  if (!adminFolder) return res.status(404).json({ error: 'Admin folder not found' });
  const fp = path.join(INTERNAL_ROOT, adminFolder, filename);
  if (!fs.existsSync(fp)) return res.status(404).json({ error: 'File no longer exists' });
  res.setHeader('Content-Type', 'application/octet-stream');
  res.setHeader('Content-Disposition', `attachment; filename="${filename}"`);
  res.sendFile(fp);
});

// ════════════════════════════════════════════════════════════════════════════
//  DIRECT MESSAGE (DM) APIs
// ════════════════════════════════════════════════════════════════════════════
function normalizeUsername(username) {
  return String(username || '').toLowerCase().trim();
}

function getThreadKey(a, b) {
  return [normalizeUsername(a), normalizeUsername(b)].sort().join('::');
}

function canUsersDM(users, a, b) {
  const ua = users[a];
  const ub = users[b];
  if (!ua || !ub) return false;
  if (a === b) return false;
  if ((ua.role || 'user') === 'user' || (ub.role || 'user') === 'user') return true;

  if (ua.role === 'admin' && ub.createdBy === a) return true;
  if (ub.role === 'admin' && ua.createdBy === b) return true;
  if (ua.role === 'student' && ub.role === 'student' && ua.createdBy && ua.createdBy === ub.createdBy) return true;

  return false;
}

function listDMContacts(users, username) {
  return Object.keys(users)
    .filter(u => u !== username && canUsersDM(users, username, u))
    .map(u => enrichProfile(u, users));
}

function chatAttachmentKind(mime, filename) {
  const ext = path.extname(filename || '').toLowerCase();
  if ((mime || '').startsWith('audio/')) return 'audio';
  if ((mime || '').startsWith('video/')) return 'video';
  if ((mime || '').startsWith('image/')) return ext === '.gif' || mime === 'image/gif' ? 'gif' : 'image';
  return 'document';
}

function pruneUploadedFiles(files) {
  for (const f of (files || [])) {
    if (f?.path && fs.existsSync(f.path)) {
      try { fs.unlinkSync(f.path); } catch {}
    }
  }
}

const dmUpload = multer({
  storage: multer.diskStorage({
    destination: (r, f, cb) => cb(null, CHAT_ATTACHMENTS_DIR),
    filename: (r, f, cb) => {
      const ext = path.extname(f.originalname).toLowerCase() || '.bin';
      cb(null, crypto.randomBytes(18).toString('hex') + ext);
    }
  }),
  limits: { fileSize: 25 * 1024 * 1024 },
  fileFilter: (r, f, cb) => {
    const allowedMimes = new Set([
      'image/png', 'image/jpeg', 'image/gif', 'image/webp', 'image/svg+xml', 'image/avif',
      'audio/mpeg', 'audio/wav', 'audio/ogg', 'audio/webm', 'audio/mp4', 'audio/x-m4a',
      'video/mp4', 'video/webm',
      'application/pdf', 'text/plain',
      'application/msword',
      'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
      'application/vnd.ms-powerpoint',
      'application/vnd.openxmlformats-officedocument.presentationml.presentation',
      'application/zip',
      'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
      'application/vnd.ms-excel'
    ]);
    const allowedExts = new Set([
      '.png', '.jpg', '.jpeg', '.gif', '.webp', '.svg', '.avif',
      '.mp3', '.wav', '.ogg', '.webm', '.m4a',
      '.mp4',
      '.pdf', '.txt', '.doc', '.docx', '.ppt', '.pptx', '.xls', '.xlsx', '.zip'
    ]);
    const ext = path.extname(f.originalname || '').toLowerCase();
    if (allowedMimes.has(f.mimetype) || allowedExts.has(ext)) return cb(null, true);
    cb(new Error('Unsupported attachment type'), false);
  }
});

app.get('/api/chat/contacts', authRequired, (req, res) => {
  const users = loadUsers();
  const me = req.user.username;
  const data = loadChatData();
  const contacts = listDMContacts(users, me).map(c => {
    const key = getThreadKey(me, c.username);
    const thread = data.messages
      .filter(m => m.threadKey === key)
      .sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp));
    const last = thread[0] || null;
    const unread = thread.filter(m => m.to === me && !(m.readBy || []).includes(me)).length;
    return {
      ...c,
      unreadCount: unread,
      lastMessageAt: last ? last.timestamp : null,
      lastMessage: last
        ? (last.text || ((last.attachments || []).length ? `Attachment (${(last.attachments || []).length})` : ''))
        : ''
    };
  }).sort((a, b) => {
    if (!a.lastMessageAt && !b.lastMessageAt) return a.displayName.localeCompare(b.displayName);
    if (!a.lastMessageAt) return 1;
    if (!b.lastMessageAt) return -1;
    return new Date(b.lastMessageAt) - new Date(a.lastMessageAt);
  });
  res.json(contacts);
});

app.get('/api/chat/messages/:username', authRequired, (req, res) => {
  const users = loadUsers();
  const me = req.user.username;
  const other = normalizeUsername(req.params.username);
  if (!users[other]) return res.status(404).json({ error: 'User not found' });
  if (!canUsersDM(users, me, other)) return res.status(403).json({ error: 'DM access is not allowed for this user' });

  const data = loadChatData();
  const reportsByMe = new Set(
    data.reports
      .filter(r => r.reportedBy === me && r.status === 'pending')
      .map(r => r.messageId)
  );

  const key = getThreadKey(me, other);
  const messages = data.messages
    .filter(m => m.threadKey === key)
    .sort((a, b) => new Date(a.timestamp) - new Date(b.timestamp));

  let changed = false;
  for (const m of messages) {
    if (m.to === me) {
      if (!Array.isArray(m.readBy)) m.readBy = [];
      if (!m.readBy.includes(me)) {
        m.readBy.push(me);
        if (!m.readAt) m.readAt = {};
        m.readAt[me] = new Date().toISOString();
        changed = true;
      }
    }
  }
  if (changed) saveChatData(data);

  // Check if other user is typing to me
  const typingKey = getThreadKey(me, other);
  const typingEntry = typingState[typingKey];
  const otherIsTyping = typingEntry && typingEntry.username === other && typingEntry.until > Date.now();

  // Find last message I sent that was read by the other person
  const myMessages = messages.filter(m => m.from === me);
  const lastSeenMsg = [...myMessages].reverse().find(m => (m.readBy || []).includes(other));
  const lastSeenAt = lastSeenMsg ? lastSeenMsg.readAt?.[other] || lastSeenMsg.timestamp : null;

  res.json({
    contact: enrichProfile(other, users),
    typing: otherIsTyping,
    lastSeenAt: lastSeenAt,
    messages: messages.map(m => ({
      id: m.id,
      from: m.from,
      to: m.to,
      text: m.text || '',
      timestamp: m.timestamp,
      mine: m.from === me,
      seen: m.from === me && (m.readBy || []).includes(other),
      attachments: (m.attachments || []).map(a => ({
        id: a.id,
        name: a.name,
        mime: a.mime,
        size: a.size,
        kind: a.kind || chatAttachmentKind(a.mime, a.name),
        url: `/api/chat/attachments/${a.id}`
      })),
      canReport: m.from !== me,
      reported: reportsByMe.has(m.id)
    }))
  });
});

// ── TYPING INDICATOR ──
app.post('/api/chat/typing/:username', authRequired, (req, res) => {
  const me = req.user.username;
  const other = normalizeUsername(req.params.username);
  const key = getThreadKey(me, other);
  typingState[key] = { username: me, until: Date.now() + 4000 };
  res.json({ success: true });
});

app.post('/api/chat/messages', authRequired, dmUpload.array('files', 8), (req, res) => {
  const users = loadUsers();
  const from = req.user.username;
  const to = normalizeUsername(req.body.to);
  const text = String(req.body.text || '').trim();
  const files = req.files || [];

  if (!to || !users[to]) {
    pruneUploadedFiles(files);
    return res.status(404).json({ error: 'Recipient not found' });
  }
  if (!canUsersDM(users, from, to)) {
    pruneUploadedFiles(files);
    return res.status(403).json({ error: 'DM access is not allowed for this user' });
  }
  if (!text && files.length === 0) {
    pruneUploadedFiles(files);
    return res.status(400).json({ error: 'Message text or attachment is required' });
  }

  const data = loadChatData();
  const message = {
    id: crypto.randomBytes(16).toString('hex'),
    threadKey: getThreadKey(from, to),
    from,
    to,
    text: text.substring(0, 2000),
    timestamp: new Date().toISOString(),
    readBy: [from],
    attachments: files.map(f => ({
      id: crypto.randomBytes(12).toString('hex'),
      storedName: f.filename,
      name: Buffer.from(f.originalname || 'attachment', 'latin1').toString('utf8').substring(0, 180),
      mime: f.mimetype || 'application/octet-stream',
      size: f.size || 0,
      kind: chatAttachmentKind(f.mimetype, f.originalname)
    }))
  };
  data.messages.push(message);
  saveChatData(data);

  res.json({
    success: true,
    message: {
      id: message.id,
      from: message.from,
      to: message.to,
      text: message.text,
      timestamp: message.timestamp,
      mine: true,
      attachments: message.attachments.map(a => ({
        id: a.id, name: a.name, mime: a.mime, size: a.size, kind: a.kind, url: `/api/chat/attachments/${a.id}`
      }))
    }
  });
});

app.get('/api/chat/attachments/:attachmentId', authRequired, (req, res) => {
  const attachmentId = req.params.attachmentId;
  const me = req.user.username;
  const data = loadChatData();
  let message = null;
  let attachment = null;
  for (const m of data.messages) {
    const found = (m.attachments || []).find(a => a.id === attachmentId);
    if (found) {
      message = m;
      attachment = found;
      break;
    }
  }
  if (!message || !attachment) return res.status(404).json({ error: 'Attachment not found' });
  if (message.from !== me && message.to !== me) return res.status(403).json({ error: 'Forbidden' });
  if (attachment.storedName.includes('..') || attachment.storedName.includes('/') || attachment.storedName.includes('\\'))
    return res.status(400).json({ error: 'Invalid attachment' });
  const filePath = path.join(CHAT_ATTACHMENTS_DIR, attachment.storedName);
  if (!fs.existsSync(filePath)) return res.status(404).json({ error: 'File not found' });
  res.setHeader('Content-Type', attachment.mime || 'application/octet-stream');
  res.setHeader('Content-Disposition', `inline; filename="${attachment.name || 'attachment'}"`);
  res.sendFile(filePath);
});

app.post('/api/chat/messages/:id/report', authRequired, (req, res) => {
  const reason = String(req.body.reason || '').trim();
  const details = String(req.body.details || '').trim();
  if (!reason) return res.status(400).json({ error: 'Reason is required' });

  const data = loadChatData();
  const users = loadUsers();
  const message = data.messages.find(m => m.id === req.params.id);
  if (!message) return res.status(404).json({ error: 'Message not found' });
  if (message.from !== req.user.username && message.to !== req.user.username)
    return res.status(403).json({ error: 'Cannot report this message' });
  if (message.from === req.user.username) return res.status(400).json({ error: 'Cannot report your own message' });

  const dup = data.reports.find(r => r.status === 'pending' && r.messageId === message.id && r.reportedBy === req.user.username);
  if (dup) return res.status(400).json({ error: 'This DM is already reported by you' });

  const me = users[req.user.username] || {};
  const otherUser = users[message.from] || {};
  let adminUser = null;
  if (req.user.role === 'admin') adminUser = req.user.username;
  else if (me.createdBy && users[me.createdBy] && users[me.createdBy].role === 'admin') adminUser = me.createdBy;
  else if (otherUser.role === 'admin') adminUser = message.from;
  else if (otherUser.createdBy && users[otherUser.createdBy] && users[otherUser.createdBy].role === 'admin') adminUser = otherUser.createdBy;

  data.reports.push({
    id: crypto.randomBytes(12).toString('hex'),
    type: 'dm-message',
    messageId: message.id,
    threadKey: message.threadKey,
    messageFrom: message.from,
    messageTo: message.to,
    messageText: (message.text || '').substring(0, 400),
    attachmentCount: (message.attachments || []).length,
    reportedBy: req.user.username,
    adminUser,
    reason: reason.substring(0, 120),
    details: details.substring(0, 800),
    timestamp: new Date().toISOString(),
    status: 'pending'
  });
  saveChatData(data);
  res.json({ success: true });
});

app.get('/api/admin/dm-reports', authRequired, adminRequired, (req, res) => {
  const data = loadChatData();
  const users = loadUsers();
  const items = data.reports
    .filter(r => r.status === 'pending' && (!r.adminUser || r.adminUser === req.user.username))
    .map(r => ({
      ...r,
      reporter: enrichProfile(r.reportedBy, users),
      sender: enrichProfile(r.messageFrom, users),
      receiver: enrichProfile(r.messageTo, users)
    }))
    .sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp));
  res.json(items);
});

app.post('/api/admin/dm-reports/:id/:action', authRequired, adminRequired, (req, res) => {
  const { action } = req.params;
  if (!['dismiss', 'resolve', 'delete-message'].includes(action))
    return res.status(400).json({ error: 'Invalid action' });

  const data = loadChatData();
  const report = data.reports.find(r => r.id === req.params.id);
  if (!report) return res.status(404).json({ error: 'Report not found' });
  if (report.status !== 'pending') return res.status(400).json({ error: 'Report already handled' });
  if (report.adminUser && report.adminUser !== req.user.username) return res.status(403).json({ error: 'Forbidden' });

  if (action === 'delete-message') {
    const mi = data.messages.findIndex(m => m.id === report.messageId);
    if (mi > -1) {
      const msg = data.messages[mi];
      for (const a of (msg.attachments || [])) {
        if (!a.storedName) continue;
        const fp = path.join(CHAT_ATTACHMENTS_DIR, a.storedName);
        if (fs.existsSync(fp)) { try { fs.unlinkSync(fp); } catch {} }
      }
      data.messages.splice(mi, 1);
    }
    report.status = 'resolved';
  } else {
    report.status = action === 'resolve' ? 'resolved' : 'dismissed';
  }
  report.resolvedBy = req.user.username;
  report.resolvedAt = new Date().toISOString();

  saveChatData(data);
  res.json({ success: true, status: report.status });
});

// ════════════════════════════════════════════════════════════════════════════
//  SOCIAL APIs (mini Twitter)
// ════════════════════════════════════════════════════════════════════════════
// ═══ Media upload multer ═══
const mediaUpload = multer({
  storage: multer.diskStorage({
    destination: (r, f, cb) => cb(null, MEDIA_DIR),
    filename: (r, f, cb) => {
      const ext = path.extname(f.originalname).toLowerCase() || '.jpg';
      cb(null, crypto.randomBytes(16).toString('hex') + ext);
    }
  }),
  limits: { fileSize: 10 * 1024 * 1024 },
  fileFilter: (r, f, cb) => {
    const ok = ['image/png','image/jpeg','image/gif','image/webp','image/svg+xml'].includes(f.mimetype);
    cb(ok ? null : new Error('Only images/GIFs allowed'), ok);
  }
});

app.get('/api/media/:filename', (req, res) => {
  const fn = req.params.filename;
  if (fn.includes('..') || fn.includes('/')) return res.status(400).end();
  const fp = path.join(MEDIA_DIR, fn);
  if (!fs.existsSync(fp)) return res.status(404).end();
  const ext = path.extname(fn).toLowerCase();
  const mime = {'.png':'image/png','.jpg':'image/jpeg','.jpeg':'image/jpeg','.gif':'image/gif','.webp':'image/webp','.svg':'image/svg+xml'};
  res.setHeader('Content-Type', mime[ext] || 'application/octet-stream');
  res.setHeader('Cache-Control', 'public, max-age=604800');
  res.sendFile(fp);
});

// ═══ Social helpers ═══
function areFriends(data, a, b) {
  return (data.friends[a] || []).includes(b);
}
function isFollowing(data, follower, target) {
  return (data.follows[follower] || []).includes(target);
}
function canViewPost(data, post, viewerUsername, viewerRole, users) {
  if (viewerRole === 'admin') return true;
  if (post.author === viewerUsername) return true;
  const authorUser = users[post.author];
  if (authorUser && authorUser.role === 'admin') return true; // admin posts public
  if (post.visibility === 'public') return true;
  return areFriends(data, viewerUsername, post.author);
}
function enrichProfile(username, users) {
  const u = users[username] || {};
  return {
    username,
    displayName: u.displayName || username,
    handle: u.handle || '@' + username.replace(/[^a-z0-9_]/g, ''),
    avatar: u.avatarFile ? `/api/avatars/${u.avatarFile}` : null,
    role: u.role || 'user'
  };
}
function totalReactions(post) {
  if (!post.reactions) return 0;
  return Object.values(post.reactions).reduce((s, arr) => s + arr.length, 0);
}
const REACTION_TYPES = ['like','love','haha','wow','sad','angry'];

// ══════════════════════════════════════════════════════════════════════
//  SOCIAL APIs — Posts, Reactions, Comments, Follow, Friends, Reports
// ══════════════════════════════════════════════════════════════════════

// ── GET posts (privacy-filtered) ──
app.get('/api/social/posts', authRequired, (req, res) => {
  const data = loadSocialData();
  const users = loadUsers();
  const me = req.user.username;
  const tab = req.query.tab; // feed | explore | bookmarks | user
  const targetUser = req.query.user;

  let posts = data.posts.filter(p => canViewPost(data, p, me, req.user.role, users));

  if (tab === 'bookmarks') {
    const bk = data.bookmarks[me] || [];
    posts = posts.filter(p => bk.includes(p.id));
  } else if (tab === 'user' && targetUser) {
    posts = posts.filter(p => p.author === targetUser);
  } else if (tab === 'feed') {
    const following = data.follows[me] || [];
    const friendsList = data.friends[me] || [];
    const relevant = new Set([me, ...following, ...friendsList]);
    posts = posts.filter(p => relevant.has(p.author));
  }
  // else 'explore' = all visible posts

  const bk = new Set(data.bookmarks[me] || []);

  const enriched = posts.map(p => {
    const isOwn = p.author === me;
    const isAdminOfAuthor = req.user.role === 'admin' && getAdminOf(p.author) === me;
    return {
      ...p,
      ...enrichProfile(p.author, users),
      canDelete: isOwn || isAdminOfAuthor,
      canReport: !isOwn,
      bookmarked: bk.has(p.id),
      myReactions: REACTION_TYPES.filter(t => (p.reactions[t] || []).includes(me)),
      reactionCounts: Object.fromEntries(REACTION_TYPES.map(t => [t, (p.reactions[t] || []).length])),
      totalReactions: totalReactions(p),
      comments: (p.comments || []).map(c => {
        const cIsOwn = c.author === me;
        const cIsAdmin = req.user.role === 'admin' && getAdminOf(c.author) === me;
        return { ...c, ...enrichProfile(c.author, users), canDelete: cIsOwn || cIsAdmin };
      })
    };
  }).sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp));
  res.json(enriched);
});

// ── CREATE post (with optional media) ──
app.post('/api/social/posts', authRequired, mediaUpload.array('media', 4), (req, res) => {
  const content = (req.body.content || '').trim();
  const files = req.files || [];
  if (!content && files.length === 0) return res.status(400).json({ error: 'Content or media required' });
  const data = loadSocialData();
  const isAdmin = req.user.role === 'admin';
  const post = {
    id: crypto.randomBytes(16).toString('hex'),
    author: req.user.username,
    content: content.substring(0, 2000),
    media: files.map(f => ({ type: f.mimetype.includes('gif') ? 'gif' : 'image', url: `/api/media/${f.filename}`, name: f.originalname })),
    timestamp: new Date().toISOString(),
    reactions: {}, comments: [],
    visibility: isAdmin ? 'public' : (req.body.visibility || 'friends')
  };
  // Allow GIF URL
  if (req.body.gifUrl) {
    post.media.push({ type: 'gif', url: req.body.gifUrl, name: 'GIF' });
  }
  data.posts.push(post);
  saveSocialData(data);
  res.json({ success: true, post });
});

// ── DELETE post ──
app.delete('/api/social/posts/:id', authRequired, (req, res) => {
  const data = loadSocialData();
  const idx = data.posts.findIndex(p => p.id === req.params.id);
  if (idx === -1) return res.status(404).json({ error: 'Post not found' });
  const post = data.posts[idx];
  const isOwn = post.author === req.user.username;
  const isAdminOfAuthor = req.user.role === 'admin' && getAdminOf(post.author) === req.user.username;
  if (!isOwn && !isAdminOfAuthor) return res.status(403).json({ error: 'Cannot delete this post' });
  // Clean up media files
  for (const m of (post.media || [])) {
    if (m.url && m.url.startsWith('/api/media/')) {
      const fn = m.url.split('/').pop();
      const fp = path.join(MEDIA_DIR, fn);
      if (fs.existsSync(fp)) try { fs.unlinkSync(fp); } catch {}
    }
  }
  data.posts.splice(idx, 1);
  // Also remove from bookmarks
  for (const u in data.bookmarks) { data.bookmarks[u] = data.bookmarks[u].filter(id => id !== req.params.id); }
  saveSocialData(data);
  res.json({ success: true });
});

// ── REACT to post ──
app.post('/api/social/posts/:id/react', authRequired, (req, res) => {
  const { reaction } = req.body;
  if (!REACTION_TYPES.includes(reaction)) return res.status(400).json({ error: 'Invalid reaction type' });
  const data = loadSocialData();
  const post = data.posts.find(p => p.id === req.params.id);
  if (!post) return res.status(404).json({ error: 'Post not found' });
  if (!post.reactions) post.reactions = {};
  // Remove user from all reactions first (toggle behavior)
  let wasReacted = false;
  for (const t of REACTION_TYPES) {
    if (!post.reactions[t]) post.reactions[t] = [];
    const i = post.reactions[t].indexOf(req.user.username);
    if (i > -1) { post.reactions[t].splice(i, 1); if (t === reaction) wasReacted = true; }
  }
  // Add new reaction unless toggling off
  if (!wasReacted) {
    if (!post.reactions[reaction]) post.reactions[reaction] = [];
    post.reactions[reaction].push(req.user.username);
  }
  saveSocialData(data);
  res.json({ success: true });
});

// ── COMMENTS ──
app.post('/api/social/posts/:id/comments', authRequired, (req, res) => {
  const { content } = req.body;
  if (!content || !content.trim()) return res.status(400).json({ error: 'Content required' });
  const data = loadSocialData();
  const post = data.posts.find(p => p.id === req.params.id);
  if (!post) return res.status(404).json({ error: 'Post not found' });
  if (!post.comments) post.comments = [];
  const comment = {
    id: crypto.randomBytes(12).toString('hex'),
    author: req.user.username,
    content: content.trim().substring(0, 500),
    timestamp: new Date().toISOString()
  };
  post.comments.push(comment);
  saveSocialData(data);
  res.json({ success: true, comment });
});

app.delete('/api/social/posts/:postId/comments/:commentId', authRequired, (req, res) => {
  const data = loadSocialData();
  const post = data.posts.find(p => p.id === req.params.postId);
  if (!post) return res.status(404).json({ error: 'Post not found' });
  const ci = (post.comments || []).findIndex(c => c.id === req.params.commentId);
  if (ci === -1) return res.status(404).json({ error: 'Comment not found' });
  const comment = post.comments[ci];
  const isOwn = comment.author === req.user.username;
  const isAdminOfAuthor = req.user.role === 'admin' && getAdminOf(comment.author) === req.user.username;
  if (!isOwn && !isAdminOfAuthor) return res.status(403).json({ error: 'Cannot delete this comment' });
  post.comments.splice(ci, 1);
  saveSocialData(data);
  res.json({ success: true });
});

// ── BOOKMARK ──
app.post('/api/social/posts/:id/bookmark', authRequired, (req, res) => {
  const data = loadSocialData();
  const me = req.user.username;
  if (!data.bookmarks[me]) data.bookmarks[me] = [];
  const i = data.bookmarks[me].indexOf(req.params.id);
  if (i > -1) data.bookmarks[me].splice(i, 1); else data.bookmarks[me].push(req.params.id);
  saveSocialData(data);
  res.json({ success: true, bookmarked: i === -1 });
});

// ══════════════════════════════════════════════════════════════════════
//  FOLLOW / FRIEND SYSTEM
// ══════════════════════════════════════════════════════════════════════
app.post('/api/social/follow/:username', authRequired, (req, res) => {
  const target = req.params.username.toLowerCase().trim();
  if (target === req.user.username) return res.status(400).json({ error: 'Cannot follow yourself' });
  const users = loadUsers();
  if (!users[target]) return res.status(404).json({ error: 'User not found' });
  const data = loadSocialData();
  const me = req.user.username;
  if (!data.follows[me]) data.follows[me] = [];
  const i = data.follows[me].indexOf(target);
  if (i > -1) data.follows[me].splice(i, 1); else data.follows[me].push(target);
  saveSocialData(data);
  res.json({ success: true, following: i === -1 });
});

app.get('/api/social/following', authRequired, (req, res) => {
  const data = loadSocialData();
  const users = loadUsers();
  const list = (data.follows[req.user.username] || []).map(u => enrichProfile(u, users));
  res.json(list);
});

app.get('/api/social/followers', authRequired, (req, res) => {
  const data = loadSocialData();
  const users = loadUsers();
  const me = req.user.username;
  const list = Object.entries(data.follows)
    .filter(([, arr]) => arr.includes(me))
    .map(([u]) => enrichProfile(u, users));
  res.json(list);
});

// ── FRIEND REQUESTS ──
app.post('/api/social/friend-request', authRequired, (req, res) => {
  const { username } = req.body;
  const target = (username || '').toLowerCase().trim();
  const me = req.user.username;
  if (target === me) return res.status(400).json({ error: 'Cannot friend yourself' });
  const users = loadUsers();
  if (!users[target]) return res.status(404).json({ error: 'User not found' });
  const data = loadSocialData();
  if (areFriends(data, me, target)) return res.status(400).json({ error: 'Already friends' });
  const existing = data.friendRequests.find(r => r.status === 'pending' && ((r.from === me && r.to === target) || (r.from === target && r.to === me)));
  if (existing) {
    // If they sent us a request, auto-accept
    if (existing.from === target) {
      existing.status = 'accepted';
      if (!data.friends[me]) data.friends[me] = [];
      if (!data.friends[target]) data.friends[target] = [];
      if (!data.friends[me].includes(target)) data.friends[me].push(target);
      if (!data.friends[target].includes(me)) data.friends[target].push(me);
      saveSocialData(data);
      return res.json({ success: true, autoAccepted: true });
    }
    return res.status(400).json({ error: 'Request already pending' });
  }
  data.friendRequests.push({
    id: crypto.randomBytes(12).toString('hex'),
    from: me, to: target,
    timestamp: new Date().toISOString(),
    status: 'pending'
  });
  saveSocialData(data);
  res.json({ success: true });
});

app.get('/api/social/friend-requests', authRequired, (req, res) => {
  const data = loadSocialData();
  const users = loadUsers();
  const me = req.user.username;
  const incoming = data.friendRequests.filter(r => r.to === me && r.status === 'pending')
    .map(r => ({ ...r, ...enrichProfile(r.from, users) }));
  const outgoing = data.friendRequests.filter(r => r.from === me && r.status === 'pending')
    .map(r => ({ ...r, ...enrichProfile(r.to, users) }));
  res.json({ incoming, outgoing });
});

app.post('/api/social/friend-requests/:id/:action', authRequired, (req, res) => {
  const { action } = req.params;
  if (!['accept','reject'].includes(action)) return res.status(400).json({ error: 'Invalid action' });
  const data = loadSocialData();
  const fr = data.friendRequests.find(r => r.id === req.params.id && r.to === req.user.username && r.status === 'pending');
  if (!fr) return res.status(404).json({ error: 'Request not found' });
  fr.status = action === 'accept' ? 'accepted' : 'rejected';
  if (action === 'accept') {
    const me = req.user.username;
    if (!data.friends[me]) data.friends[me] = [];
    if (!data.friends[fr.from]) data.friends[fr.from] = [];
    if (!data.friends[me].includes(fr.from)) data.friends[me].push(fr.from);
    if (!data.friends[fr.from].includes(me)) data.friends[fr.from].push(me);
  }
  saveSocialData(data);
  res.json({ success: true, status: fr.status });
});

app.get('/api/social/friends', authRequired, (req, res) => {
  const data = loadSocialData();
  const users = loadUsers();
  const list = (data.friends[req.user.username] || []).map(u => enrichProfile(u, users));
  res.json(list);
});

app.delete('/api/social/friends/:username', authRequired, (req, res) => {
  const target = req.params.username.toLowerCase().trim();
  const me = req.user.username;
  const data = loadSocialData();
  data.friends[me] = (data.friends[me] || []).filter(u => u !== target);
  data.friends[target] = (data.friends[target] || []).filter(u => u !== me);
  saveSocialData(data);
  res.json({ success: true });
});

// ── USER SOCIAL PROFILE ──
app.get('/api/social/users/search', authRequired, (req, res) => {
  const q = (req.query.q || '').toLowerCase().trim();
  if (!q) return res.json([]);
  const users = loadUsers();
  const data = loadSocialData();
  const me = req.user.username;
  const results = Object.keys(users)
    .filter(u => u !== me && (u.includes(q) || (users[u].displayName || '').toLowerCase().includes(q) || (users[u].handle || '').toLowerCase().includes(q)))
    .slice(0, 20)
    .map(u => {
      const p = enrichProfile(u, users);
      p.isFollowing = isFollowing(data, me, u);
      p.isFriend = areFriends(data, me, u);
      p.hasPendingRequest = data.friendRequests.some(r => r.status === 'pending' && ((r.from === me && r.to === u) || (r.from === u && r.to === me)));
      p.followersCount = Object.values(data.follows).filter(arr => arr.includes(u)).length;
      p.followingCount = (data.follows[u] || []).length;
      p.friendsCount = (data.friends[u] || []).length;
      p.postCount = data.posts.filter(post => post.author === u).length;
      return p;
    });
  res.json(results);
});

app.get('/api/social/users/:username', authRequired, (req, res) => {
  const target = req.params.username.toLowerCase().trim();
  const users = loadUsers();
  if (!users[target]) return res.status(404).json({ error: 'User not found' });
  const data = loadSocialData();
  const me = req.user.username;
  const p = enrichProfile(target, users);
  p.isFollowing = isFollowing(data, me, target);
  p.isFriend = areFriends(data, me, target);
  p.hasPendingRequest = data.friendRequests.some(r => r.status === 'pending' && ((r.from === me && r.to === target) || (r.from === target && r.to === me)));
  p.followersCount = Object.values(data.follows).filter(arr => arr.includes(target)).length;
  p.followingCount = (data.follows[target] || []).length;
  p.friendsCount = (data.friends[target] || []).length;
  p.postCount = data.posts.filter(post => post.author === target).length;
  p.isMe = target === me;
  res.json(p);
});

// ── REPORT POST ──
app.post('/api/social/posts/:id/report', authRequired, (req, res) => {
  const { reason } = req.body;
  if (!reason || !reason.trim()) return res.status(400).json({ error: 'Reason required' });
  const data = loadSocialData();
  const post = data.posts.find(p => p.id === req.params.id);
  if (!post) return res.status(404).json({ error: 'Post not found' });
  if (post.author === req.user.username) return res.status(400).json({ error: 'Cannot report own post' });
  // Prevent duplicate reports
  const dup = data.reports.find(r => r.postId === req.params.id && r.reportedBy === req.user.username && r.status === 'pending');
  if (dup) return res.status(400).json({ error: 'Already reported' });
  data.reports.push({
    id: crypto.randomBytes(12).toString('hex'),
    postId: req.params.id,
    postAuthor: post.author,
    postContent: post.content.substring(0, 200),
    reportedBy: req.user.username,
    reason: reason.trim().substring(0, 500),
    timestamp: new Date().toISOString(),
    status: 'pending'
  });
  saveSocialData(data);
  res.json({ success: true });
});

// ── ADMIN: Reports ──
app.get('/api/admin/reports', authRequired, adminRequired, (req, res) => {
  const data = loadSocialData();
  const users = loadUsers();
  const pending = data.reports.filter(r => r.status === 'pending').map(r => ({
    ...r,
    reporter: enrichProfile(r.reportedBy, users),
    author: enrichProfile(r.postAuthor, users)
  }));
  res.json(pending);
});

app.post('/api/admin/reports/:id/:action', authRequired, adminRequired, (req, res) => {
  const { action } = req.params;
  if (!['dismiss','delete-post'].includes(action)) return res.status(400).json({ error: 'Invalid action' });
  const data = loadSocialData();
  const report = data.reports.find(r => r.id === req.params.id);
  if (!report) return res.status(404).json({ error: 'Report not found' });
  if (action === 'delete-post') {
    const pi = data.posts.findIndex(p => p.id === report.postId);
    if (pi > -1) {
      const post = data.posts[pi];
      for (const m of (post.media || [])) {
        if (m.url && m.url.startsWith('/api/media/')) {
          const fn = m.url.split('/').pop();
          const fp = path.join(MEDIA_DIR, fn);
          if (fs.existsSync(fp)) try { fs.unlinkSync(fp); } catch {}
        }
      }
      data.posts.splice(pi, 1);
    }
    // Remove all reports for this post
    data.reports = data.reports.filter(r => r.postId !== report.postId);
  } else {
    report.status = 'dismissed';
  }
  saveSocialData(data);
  res.json({ success: true });
});

app.get('/api/secret', (req, res) => {
  const secrets = [
    "The cake is a lie. But this PDF viewer is real. \ud83c\udf82",
    "You found the secret API! You must be a developer. \ud83e\uddd1\u200d\ud83d\udcbb",
    "42 - The answer to life, the universe, and document management.",
    "There are 10 types of people: those who understand binary, and those who don't.",
    "// TODO: Add more easter eggs (this has been here since 2024)",
    "Prenxy was built with \u2764\ufe0f and probably too much caffeine.",
    "sudo make me a sandwich \ud83e\udd6a",
    "Have you tried turning your PDF off and on again?",
    "The mitochondria is the powerhouse of the cell. PDFs are the powerhouse of knowledge.",
    "QuantumTunneling: where your documents pass through barriers effortlessly \u269b\ufe0f"
  ];
  res.json({ message: secrets[Math.floor(Math.random() * secrets.length)], found: true });
});

app.use((err, req, res, next) => {
  if (err instanceof multer.MulterError) return res.status(400).json({ error: err.message });
  if (err) return res.status(400).json({ error: err.message });
  next();
});

function getLocalIP() {
  const interfaces = os.networkInterfaces();
  for (const name of Object.keys(interfaces)) {
    for (const iface of interfaces[name]) {
      if (iface.family === 'IPv4' && !iface.internal) return iface.address;
    }
  }
  return '0.0.0.0';
}

// ════════════════════════════════════════════════════════════════════════════
//  CLI COMMANDS — run with: node server.js <command> [args]
//    create-account <username> <password>
//    create-admin <username> <password>
//    create-slave <adminUsername> <username> <password>
//    create-user <username> <password>
//    delete-account <username>
//    list-accounts
//    list-slaves [adminUsername]
//    reset-password <username> <new-password>
//    migrate-documents [target-username]
// ════════════════════════════════════════════════════════════════════════════
const args = process.argv.slice(2);

if (args.length > 0) {
  const command = args[0];
  writeActionLog('cli.command', { command: maskSensitiveCommand(args.join(' ')) }, 'cli');

  switch (command) {
    case 'create-account': {
      if (args.length < 3) { console.error('Usage: node server.js create-account <username> <password>'); process.exit(1); }
      const result = createAccountWithRole({ username: args[1], password: args[2], role: 'user' });
      if (result.success) {
        logInfo(`Account created: ${result.username} (role=${result.role})`);
        logInfo(`Storage path: .internal_root/${result.folderHash}/`);
      } else {
        logError(result.error);
      }
      process.exit(0);
    }

    case 'create-admin': {
      if (args.length < 3) { console.error('Usage: node server.js create-admin <username> <password>'); process.exit(1); }
      const result = createAccountWithRole({ username: args[1], password: args[2], role: 'admin' });
      if (result.success) logInfo(`Admin account created: ${result.username}`);
      else logError(result.error);
      process.exit(result.success ? 0 : 1);
    }

    case 'create-slave': {
      if (args.length < 4) { console.error('Usage: node server.js create-slave <adminUsername> <username> <password>'); process.exit(1); }
      const users = loadUsers();
      const parentAdmin = normalizeAccountUsername(args[1]);
      if (!users[parentAdmin] || (users[parentAdmin].role || 'user') !== 'admin') {
        logError(`Admin not found: ${parentAdmin}`);
        process.exit(1);
      }
      const result = createAccountWithRole({ username: args[2], password: args[3], role: 'student', createdBy: parentAdmin });
      if (result.success) logInfo(`Slave/student account created: ${result.username} (admin=${parentAdmin})`);
      else logError(result.error);
      process.exit(result.success ? 0 : 1);
    }

    case 'create-user': {
      if (args.length < 3) { console.error('Usage: node server.js create-user <username> <password>'); process.exit(1); }
      const result = createAccountWithRole({ username: args[1], password: args[2], role: 'user' });
      if (result.success) logInfo(`User account created: ${result.username}`);
      else logError(result.error);
      process.exit(result.success ? 0 : 1);
    }

    case 'delete-account': {
      if (args.length < 2) { console.error('Usage: node server.js delete-account <username>'); process.exit(1); }
      const result = deleteAccount(args[1]);
      if (result.success) {
        logInfo(`Account deleted: ${args[1]}`);
        logWarn('User files are not deleted automatically.');
      } else {
        logError(result.error);
      }
      process.exit(0);
    }

    case 'list-accounts': {
      const accounts = listAccounts();
      if (accounts.length === 0) { logInfo('No accounts found.'); }
      else accounts.forEach(acc => logInfo(`${acc.username} role=${acc.role || 'user'} createdAt=${acc.createdAt || 'unknown'}`));
      process.exit(0);
    }

    case 'list-slaves': {
      const users = loadUsers();
      const adminUser = normalizeAccountUsername(args[1] || '');
      const rows = Object.entries(users)
        .filter(([u, data]) => (data.role || 'user') === 'student' && (!adminUser || data.createdBy === adminUser))
        .map(([u, data]) => ({ username: u, createdBy: data.createdBy || '-', createdAt: data.createdAt || '' }))
        .sort((a, b) => a.username.localeCompare(b.username));
      if (!rows.length) logInfo('No slave/student accounts found.');
      else rows.forEach(r => logInfo(`${r.username} admin=${r.createdBy} createdAt=${r.createdAt}`));
      process.exit(0);
    }

    case 'show-logs': {
      const count = Math.max(1, Math.min(parseInt(args[1], 10) || 30, 300));
      const logs = readActionLogs(count);
      if (!logs.length) {
        logInfo('No action logs yet.');
      } else {
        logs.forEach(item => {
          console.log(`${item.timestamp} actor=${item.actor} action=${item.action} details=${JSON.stringify(item.details || {})}`);
        });
      }
      process.exit(0);
    }

    case 'reset-password': {
      if (args.length < 3) { console.error('Usage: node server.js reset-password <username> <new-password>'); process.exit(1); }
      const users = loadUsers();
      const uid = args[1].toLowerCase().trim();
      if (!users[uid]) { console.error(`\u274c Account not found: ${args[1]}`); process.exit(1); }
      const { hash, salt } = hashPassword(args[2]);
      users[uid].passwordHash = hash;
      users[uid].salt = salt;
      saveUsers(users);
      writeActionLog('account.reset-password', { username: uid }, 'cli');
      logInfo(`Password reset for: ${uid}`);
      process.exit(0);
    }

    case 'migrate-documents': {
      const oldDocsDir = path.join(__dirname, 'documents');
      if (!fs.existsSync(oldDocsDir)) { console.log('No documents/ folder found. Nothing to migrate.'); process.exit(0); }
      const accounts = listAccounts();
      if (accounts.length === 0) {
        console.error('\u274c No accounts exist. Create an account first:');
        console.error('   node server.js create-account <username> <password>');
        process.exit(1);
      }
      const targetUser = args[1] || accounts[0].username;
      const users = loadUsers();
      const uid = targetUser.toLowerCase().trim();
      if (!users[uid]) { console.error(`\u274c Account not found: ${targetUser}`); process.exit(1); }
      const targetDir = path.join(INTERNAL_ROOT, users[uid].folderHash);
      if (!fs.existsSync(targetDir)) fs.mkdirSync(targetDir, { recursive: true });
      const files = fs.readdirSync(oldDocsDir).filter(f => {
        const fp = path.join(oldDocsDir, f);
        return fs.statSync(fp).isFile() && f !== 'README.md';
      });
      let migrated = 0;
      for (const file of files) {
        const src = path.join(oldDocsDir, file);
        const dest = path.join(targetDir, file);
        try { fs.copyFileSync(src, dest); migrated++; process.stdout.write(`  \ud83d\udcc4 Migrated: ${file}\n`); }
        catch (e) { console.error(`  \u274c Failed: ${file} \u2014 ${e.message}`); }
      }
      console.log(`\n\u2705 Migrated ${migrated}/${files.length} files to ${targetUser} (.internal_root/${users[uid].folderHash}/)`);
      console.log('   You can now safely remove the old documents/ folder.');
      process.exit(0);
    }

    case 'set-role': {
      if (args.length < 3) { console.error('Usage: node server.js set-role <username> <admin|slave|student|user>'); process.exit(1); }
      const users = loadUsers();
      const uid = args[1].toLowerCase().trim();
      const role = normalizeAccountRole(args[2]);
      if (!role) { console.error('❌ Role must be: admin, slave/student, or user'); process.exit(1); }
      if (!users[uid]) { console.error(`❌ Account not found: ${args[1]}`); process.exit(1); }
      users[uid].role = role;
      if (role === 'student' && args[3]) users[uid].createdBy = normalizeAccountUsername(args[3]);
      saveUsers(users);
      writeActionLog('account.set-role', { username: uid, role, createdBy: users[uid].createdBy || null }, 'cli');
      logInfo(`Role set: ${uid} -> ${role}`);
      process.exit(0);
    }

    default:
      writeActionLog('cli.command.unknown', { command }, 'cli');
      console.error(`Unknown command: ${command}`);
      console.log('\nAvailable commands:');
      console.log('  create-account <username> <password>');
      console.log('  create-admin <username> <password>');
      console.log('  create-slave <adminUsername> <username> <password>');
      console.log('  create-user <username> <password>');
      console.log('  delete-account <username>');
      console.log('  list-accounts');
      console.log('  list-slaves [adminUsername]');
      console.log('  show-logs [count]');
      console.log('  reset-password <username> <new-password>');
      console.log('  set-role <username> <admin|slave|student|user> [adminUsernameForSlave]');
      console.log('  migrate-documents [target-username]');
      console.log('\nTo start the server, run: node server.js');
      process.exit(1);
  }
}

// ═══════ Start server ═══════
app.listen(PORT, '0.0.0.0', () => {
  const localIP = getLocalIP();
  const accounts = listAccounts();
  logInfo('Prenxy server started');
  logInfo(`Local URL   : http://localhost:${PORT}`);
  logInfo(`Network URL : http://${localIP}:${PORT}`);
  logInfo(`Storage root: ${INTERNAL_ROOT}`);
  logInfo(`Accounts    : ${accounts.length}`);
  logInfo('CLI quick commands:');
  logInfo('  node server.js list-accounts');
  logInfo('  node server.js create-admin <username> <password>');
  logInfo('  node server.js show-logs 30');
  writeActionLog('server.start', {
    port: PORT,
    local: `http://localhost:${PORT}`,
    network: `http://${localIP}:${PORT}`,
    accounts: accounts.length
  }, 'system');
  const recent = readActionLogs(5);
  if (recent.length) {
    logInfo('Recent actions:');
    recent.forEach(item => {
      console.log(`${item.timestamp} actor=${item.actor} action=${item.action} details=${JSON.stringify(item.details || {})}`);
    });
  }
});
