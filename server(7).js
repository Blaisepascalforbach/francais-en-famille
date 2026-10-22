import 'dotenv/config';
import express from 'express';
import multer from 'multer';
import mammoth from 'mammoth';
import { readFileSync } from 'fs';
import crypto from 'crypto';
import pdf from 'pdf-parse/lib/pdf-parse.js';
import { toolsFor, lexiconFor, pdfTextMath, lexiconAll, mathsNotes, leakValues, lexAnswer, readingVerdict, sansRaccourci, bareNumber, askedNumber, readingAsk, mathSigns, pupilValue, solveVerdict, answerForms, questionText, isQuestion, calcValue, qcmOption } from './maths.js';
import { intentOf, isHelpIntent, helpLevel, helpNote, situationNote, unknownNote, issuesOf, repair, pick } from './dialogue.js';
import { sanitizeTrack, currentQuestion, nextQuestion, firstQuestion, PLAN_SYSTEM, planUser, checkPlan, planTurn, planLeaks, looseValue, qKey } from './pedagogie.js';
import { toPassages } from './passages.js';

const { ALBERT_API_KEY, ALBERT_BASE_URL, ALBERT_MODEL, ALBERT_VISION_MODEL } = process.env;
const app = express();
app.set('trust proxy', 1); // derrière l'hébergeur : l'adresse IP réelle de l'élève est lue correctement
app.use((_q, res, next) => { res.setHeader('X-Content-Type-Options', 'nosniff'); res.setHeader('Referrer-Policy', 'no-referrer'); res.setHeader('X-Frame-Options', 'DENY'); next(); });
app.use(express.json({ limit: '6mb' }));
// PDF.js servi localement (aucun CDN : le document de l'élève ne quitte pas l'application)
app.use('/vendor/pdfjs', express.static('node_modules/pdfjs-dist/build', { setHeaders: (res, p) => { if (p.endsWith('.mjs')) res.type('text/javascript'); } }));
app.use('/vendor/katex', express.static('node_modules/katex/dist')); // affichage des fractions, puissances et racines
app.use(express.static('public', { setHeaders: res => res.setHeader('Cache-Control', 'no-cache') })); // jamais d'ancienne page en cache
// Fichiers gardés en mémoire uniquement : rien n'est écrit sur le disque (RGPD)
const upload = multer({ storage: multer.memoryStorage(), limits: { fileSize: 15 * 1024 * 1024 } });

// ---------- Protection de l'accès (version hébergée) ----------
const { ACCESS_CODE } = process.env;
const RATE = +process.env.RATE_PER_MIN || 40;      // demandes par minute et par appareil
const DAILY = +process.env.DAILY_CALLS || 3000;    // appels au modèle par jour, pour tous les élèves ensemble
const hash = x => crypto.createHash('sha256').update(String(x)).digest();
const sameCode = (a, b) => crypto.timingSafeEqual(hash(a), hash(b));
const hits = new Map();
setInterval(() => { const t = Date.now(); for (const [k, v] of hits) if (t - v.t > 600000) hits.delete(k); }, 300000).unref();
const hit = (k, windowMs) => { const t = Date.now(), h = hits.get(k) || { n: 0, t }; if (t - h.t > windowMs) { h.n = 0; h.t = t; } h.n++; hits.set(k, h); return h.n; };
function gate(req, res, next) {
  if (req.path === '/health') return next();
  if (ACCESS_CODE && !sameCode(req.get('x-access-code') || (req.path === '/diag' ? String(req.query.code || '') : ''), ACCESS_CODE)) {
    if (hit('bad:' + req.ip, 600000) > 20) return res.status(429).json({ error: 'Trop d\'essais. Réessaie dans quelques minutes.' });
    return res.status(401).json({ error: "Code d'accès requis." });
  }
  if (hit('ip:' + req.ip, 60000) > RATE) return res.status(429).json({ error: 'Tu vas trop vite. Attends une minute.' });
  next();
}
let budgetDay = new Date().toDateString(), budgetCalls = 0;
function budget() {
  const d = new Date().toDateString(); if (d !== budgetDay) { budgetDay = d; budgetCalls = 0; }
  if (++budgetCalls > DAILY) throw new Error("La limite d'utilisation du jour est atteinte. Réessaie demain ou préviens ton professeur.");
}
app.use('/api', gate);

const LANGS = { ar: 'arabe', tr: 'turc', uk: 'ukrainien', fr: 'aucune pour le moment (l\'élève n\'a pas choisi de langue d\'appui)' };
const NOL1 = l1 => l1 === 'fr'; // pas de langue d'appui choisie : aucune traduction
const trad = l1 => (NOL1(l1) ? 'chaîne vide "" (pas de langue d\'appui choisie)' : `traduction fidèle en ${LANGS[l1]}`);

const pause = ms => new Promise(r => setTimeout(r, ms));
class Busy extends Error {}
async function albert(messages, { model = ALBERT_MODEL, json = true } = {}) {
  budget();
  const call = (withFormat) => fetch(`${ALBERT_BASE_URL}/chat/completions`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', Authorization: `Bearer ${ALBERT_API_KEY}` },
    body: JSON.stringify({ model, messages, temperature: 0.3, ...(withFormat ? { response_format: { type: 'json_object' } } : {}) })
  });
  // Albert très sollicité (429) ou en difficulté (5xx) : on attend un peu et on réessaie, deux fois au plus, avant de dire quoi que ce soit à l'élève
  let r, withFormat = json;
  for (let k = 0; k < 3; k++) {
    try { r = await call(withFormat); } catch (e) { if (k === 2) throw e; await pause(1200 * (k + 1)); continue; }
    if (r.status === 400 && withFormat) { console.warn('Albert 400 avec response_format, nouvel essai sans :', (await r.text()).slice(0, 300)); withFormat = false; r = await call(false); }
    if (r.status !== 429 && r.status < 500) break;
    if (k < 2) { const ra = parseFloat(r.headers && r.headers.get ? r.headers.get('retry-after') : ''); console.warn(`Albert ${r.status}, nouvel essai`); await pause(Math.min(8000, Number.isFinite(ra) ? ra * 1000 : 1500 * (k + 1))); }
  }
  if (r.status === 429) { console.warn('Albert 429, détail :', (await r.text().catch(() => '')).slice(0, 400)); throw new Busy('Le tuteur est très demandé en ce moment. Attends quelques secondes, puis réessaie.'); }
  if (!r.ok) throw new Error(`Albert ${r.status} : ${(await r.text()).slice(0, 400)}`);
  const j = await r.json().catch(() => null);
  const m = j && Array.isArray(j.choices) && j.choices[0] && j.choices[0].message;
  if (!m) throw new Error('Albert : réponse vide');
  return m.content || '';
}
const clean = x => typeof x === 'string'
  ? x.replace(/\b(le |ce |du )?passages?\s+\d+/gi, 'ce passage').replace(/["«“]?\bcite[\s_]*(\d+)["»”]?/gi, '$1').replace(/\s*["«“]cite["»”]/gi, '') : x;
function parseJson(s) {
  let r;
  try { r = JSON.parse(s); } catch { const m = s.match(/\{[\s\S]*\}/); try { r = m && JSON.parse(m[0]); } catch {} }
  if (!r) r = { fr: s, l1: '', cite: [], mots: [] };
  if (r.refs && !r.cite) r.cite = r.refs;
  r.fr = clean(r.fr); r.l1 = clean(r.l1); if (r.dire) r.dire = clean(r.dire); if (r.hors !== true) delete r.hors;
  return r;
}


const words = t => (t || '').trim().split(/\s+/).filter(Boolean).length;
const CLOSED = /(comprends-tu|est-ce que tu comprends|as-tu compris|tu as compris|c'est clair|tu comprends\s*\?)/i;

// Formes verbales hors niveau (repérées par le contrôle serveur)
const SUBJ_RE = 'que (?:je |tu |il |elle |on |nous |vous |ils |elles )?(?:soit|soient|sois|soyons|soyez|ait|aient|aies|ayons|ayez|fasse|fassent|puisse|puissent|veuille|aille|sache|vienne|prenne)';
const PS_RE = '(?:nous|vous) \\w+(?:âmes|âtes|îmes|îtes|ûmes|ûtes)'; // passé simple 1re/2e personne du pluriel (la 3e personne -èrent ne se distingue pas du présent de espérer, préférer…)
const COND_RE = '(?!portrait|trait|attrait|retrait|distrait|extrait|abstrait)\\w+(?:rait|raient)';
// ---------- Niveaux CECRL : le tuteur ET le contrôle serveur s'y réfèrent ----------
const LEVELS = {
  'A2+': {
    diff: `DIFFÉRENCE DE NIVEAU (A2+) :
- L'élève comprend des phrases et des textes courts, concrets, sur des sujets connus ; il s'exprime avec des phrases simples reliées par « et », « mais », « parce que ».
- Toi : une seule idée par message, concrète, avec une image ou un exemple de la vie courante. Explique un mot par un exemple ou un synonyme très fréquent. Montre l'endroit exact du texte à regarder.
- Questions : qui ? où ? quand ? quoi ? ; choisir entre deux réponses ; compléter une phrase ; retrouver un mot. Pour une déduction, MONTRE l'indice puis demande la conclusion.
- Donne l'amorce de la réponse (« Je pense que… ») dès la première demande. Attends un mot, un groupe de mots ou une phrase.
- Exemple (mot « artisan ») : « Un artisan fabrique des objets avec ses mains. Par exemple, un boulanger fait du pain. Quel autre artisan connais-tu ? »`,
    diffMaths: `DIFFÉRENCE DE NIVEAU (A2+), en mathématiques. Repères CECRL : l'élève comprend des consignes courtes et concrètes, rédigées simplement ; il sait dire qu'il ne comprend pas et demander de répéter ; il fait encore des erreurs de base, mais on comprend ce qu'il veut dire.
- Toi : DÉCOMPOSE (CECRL, médiation : « décomposer une information compliquée »). UNE seule chose par message : une règle, OU une étape, OU une question. Phrases courtes, mots fréquents.
- Garde les mots de maths (fraction, dénominateur, hypoténuse…), mais un seul mot nouveau à la fois, expliqué par un exemple concret. Reprends les mots exacts de l'énoncé et montre la donnée utile (« Regarde 24. »).
- Questions : un choix entre deux (« des dixièmes ou des centièmes ? »), un nombre, un mot, un calcul court. Pas de « pourquoi » au début.
- L'élève répond par un nombre, un mot, un calcul ou une phrase très courte.
- Ses erreurs de français ne comptent pas en maths : si on comprend sa réponse, juge les maths. Reprends sa réponse correctement dans ta phrase (« Oui, un quart ! »), sans dire qu'il a fait une faute.
- Justifier (brevet) : donne une amorce à compléter (« On sait que… Donc… »).`,
    maxWords: 12, maxSentences: 2, optWords: 6, maxMots: 1, longSentences: 4,
    banned: new RegExp('\\b(?:dont|lequel|laquelle|lesquels|lesquelles|auquel|duquel|afin que|bien que|quoique|pourvu que|puisque|cependant|néanmoins|toutefois|' + SUBJ_RE + '|' + PS_RE + '|' + COND_RE + ')\\b', 'i'),
    profil: `- Phrases simples (sujet + verbe + complément), sans proposition relative complexe ni subordonnée difficile.
- Temps : présent, passé composé, futur proche (« il va… »). Pas de subjonctif, pas de conditionnel, pas de passé simple.
- Connecteurs permis : et, mais, parce que, alors, d'abord, ensuite, après.
- Lexique fréquent et concret. UN seul mot disciplinaire difficile à la fois, expliqué avec un petit exemple.
- Tu attends de l'élève un mot, un groupe de mots ou une phrase très courte, avec une amorce (« Je pense que… »).
- Tu peux ajouter UNE phrase très courte d'encouragement ou d'empathie (« C'est normal de bloquer. », « Bonne idée ! »), en plus.`
  },
  'B1': {
    diff: `DIFFÉRENCE DE NIVEAU (B1) :
- L'élève comprend l'essentiel d'un texte clair sur des sujets scolaires ; il sait raconter, expliquer, donner un avis avec des phrases reliées. Ne le traite PAS comme un débutant.
- Toi : 2 ou 3 phrases reliées (cause, opposition, but). Explique un mot par une définition en français précise, avec son contexte, un mot de la même famille ou une nuance. Vocabulaire disciplinaire plus riche (2 mots par message).
- Questions : pourquoi ? comment ? quelle différence ? que montre ce passage ? reformule ; justifie ta réponse avec une citation du texte. Pour une déduction, laisse l'élève TROUVER lui-même l'indice ; ne le montre qu'après une difficulté.
- Donne l'amorce seulement après un échec. Attends 2 ou 3 phrases reliées, avec une justification (« parce que le texte dit… »).
- Exemple (mot « artisan ») : « Un artisan est une personne qui fabrique ou répare des objets à la main, souvent dans son propre atelier. Cite un métier d'artisan et explique ce qu'il fabrique. »`,
    diffMaths: `DIFFÉRENCE DE NIVEAU (B1), en mathématiques. Repères CECRL : l'élève comprend des consignes claires et directes ; il sait demander de clarifier ou de préciser ; il communique avec une correction suffisante dans des situations familières, avec encore des erreurs. Ne le traite PAS comme un débutant.
- Toi : 2 ou 3 phrases reliées (donc, parce que, alors). Tu peux relier la règle et son usage dans la même réponse. Vocabulaire mathématique précis (2 mots par message), expliqué si besoin.
- Questions : comment ? pourquoi ? quelle règle utilises-tu ? Fais-lui expliquer sa méthode avec ses mots.
- L'élève écrit son calcul et une phrase de justification (« … parce que … »).
- Ses erreurs de français ne comptent pas en maths : reprends sa phrase correctement dans ta réponse, sans le lui reprocher.
- Justifier (brevet) : demande-lui de nommer la propriété utilisée ; donne une amorce seulement après un échec.`,
    maxWords: 18, maxSentences: 3, optWords: 8, maxMots: 2, longSentences: 5,
    banned: new RegExp('\\b(?:afin que|quoique|pourvu que|néanmoins|toutefois|lequel|laquelle|lesquels|lesquelles|auquel|duquel|' + SUBJ_RE + '|' + PS_RE + ')\\b', 'i'),
    profil: `- Phrases claires, avec des subordonnées simples (qui, que, quand, si, parce que, pour que).
- Temps : présent, passé composé, imparfait, futur simple. Conditionnel seulement pour une hypothèse simple. Pas de passé simple dans tes phrases.
- Connecteurs permis : donc, pourtant, alors que, ensuite, enfin, par exemple, mais, parce que.
- Jusqu'à 2 mots disciplinaires par message, chacun expliqué simplement.
- Tu attends de l'élève 2 ou 3 phrases reliées, qui expliquent « pourquoi » ou « comment », avec « parce que… ».`
  }
};
const lv = level => LEVELS[level] || LEVELS['A2+'];

// ---------- Matières : l'application est transversale ----------
const SUBJECTS = {
  auto: { nom: 'à déterminer d\'après le document', guide: 'Repère la matière du document (histoire, géographie, français, mathématiques, sciences, EMC…) et adapte ton aide à cette matière.', infer: 'La déduction doit s\'appuyer sur des indices du document.', hint: 'Choisis une déduction qui s\'appuie sur un indice du texte.' },
  histoire: { nom: 'histoire', guide: 'Aide à situer dans le temps (quand ?), dans l\'espace (où ?), à repérer qui fait quoi. Explique le vocabulaire historique (cité, citoyen, roi, révolution…) avec un exemple simple. Reste factuel : aucun jugement politique ni moral.', infer: 'En histoire, la déduction porte sur la cause, la conséquence, le statut social ou l\'époque.', hint: 'cause, conséquence, statut social (qui a le pouvoir ?) ou époque déduits d\'un indice du texte' },
  geographie: { nom: 'géographie', guide: 'Dis à l\'élève de lire d\'abord le titre, la légende et l\'échelle des documents. Aide à décrire un lieu (où ? comment est-ce ?) et explique les mots de géographie (relief, climat, population, densité…).', infer: 'En géographie, la déduction porte sur le climat, l\'organisation d\'un lieu ou le lien entre un paysage et les activités des habitants.', hint: 'lien entre un lieu et son climat, son relief ou les activités des habitants, déduit d\'un indice' },
  francais: { nom: 'français', guide: 'Aide à comprendre un texte littéraire ou un exercice de langue : qui parle ? où ? quand ? Les sentiments, la saison ou le lieu se DÉDUISENT d\'indices (« il grelotte » → il a froid). Pour la grammaire, donne un mini-exemple, jamais la réponse.', infer: 'En français, la déduction porte sur un sentiment, une saison, un lieu ou l\'intention d\'un personnage, à partir d\'indices.', hint: 'sentiment, saison, lieu ou intention d\'un personnage déduits d\'un indice du texte' },
  maths: { nom: 'mathématiques', guide: `Ne résous pas le problème à la place de l'élève : pas de résultat de calcul, pas de démonstration rédigée, même partielle — SAUF consigne AIDE GRADUÉE (exemple semblable avec d'autres nombres, première étape faite ensemble, correction autorisée par l'enseignant). Même pour « Montrer que… » (le résultat est déjà donné) : l'élève doit montrer COMMENT on y arrive, pas le recopier.
Aide dans cet ordre, UNE seule étape par message :
1. LA CONSIGNE : explique ce que demande le verbe (calculer, déterminer, montrer que, justifier, interpréter, lire graphiquement, arrondir…). Utilise les définitions du LEXIQUE FIABLE quand il t'est donné : ne les remplace pas par les tiennes. Quand l'élève demande le sens d'un mot, commence par reprendre ce mot avec son article (« La proportionnalité, c'est… »). Pour expliquer un mot, donne un exemple pris HORS de l'exercice (vie courante) : jamais avec les nombres de l'énoncé, jamais le coefficient ni la méthode de l'exercice.
2. LES DONNÉES : « Qu'est-ce qu'on sait ? Qu'est-ce qu'on cherche ? » (nombres, unités, noms des points).
En mathématiques, chaque question que tu poses fait AVANCER la résolution (ce qu'on cherche, la donnée utile, l'outil, la première étape) : ne demande jamais de recopier un nombre, de retrouver un mot dans la phrase ni de dire où il se trouve.
3. L'OUTIL : tu peux demander « Quelle règle connais-tu pour ça ? ». Si l'élève ne la connaît pas, l'a oubliée ou la demande, RAPPELLE-LA tout de suite, telle quelle (voir RÈGLES DU COURS), avec ses mots expliqués simplement : une règle, une formule, un théorème, c'est un savoir du cours, pas la réponse. Ne le fais jamais deviner. Ce que tu ne fais pas : l'appliquer toi-même avec les nombres de l'exercice.
4. LE CALCUL : c'est l'élève qui calcule. Si un OUTIL DE CALCUL t'est donné, appuie-toi UNIQUEMENT sur lui pour dire si c'est juste (par exemple « Oui, ton calcul est juste ! » / « Il y a une petite erreur dans une ligne : on la cherche ensemble ? »), sans donner la bonne valeur. Sans cet outil, ne dis pas si c'est juste ou faux : demande-lui son calcul, pour le vérifier ensemble.
5. LA RÉDACTION (au brevet, toute réponse doit être justifiée) : propose des amorces (« On sait que… », « Or… », « Donc… », « D'après la propriété… »).
- Quand l'élève te demande d'expliquer une question ou une consigne de l'exercice (sélection), explique seulement CE QU'ON CHERCHE (« On cherche la chance de tirer une boule bleue. »), avec les mots de l'énoncé : n'ajoute pas d'exemple chiffré pris ailleurs (pas de « comme 2/5 »). N'écris pas quelle opération faire avec les données de l'énoncé (pas de « on divise… par… », « on multiplie… », « on additionne… ») : c'est à l'élève de la trouver (sauf AIDE GRADUÉE étape 4 ou 5).
- SIGNES : écris les calculs avec les vrais signes : × pour multiplier (jamais x ni *), ÷ ou une fraction pour diviser, − pour moins, ², ³, ⁻³ pour les puissances (10⁻³), √ pour la racine, π, ≤ et ≥. Une fraction s'écrit 2/5 : l'application l'affiche comme une vraie fraction. Jamais de LaTeX ni de $.
- Lis les nombres exactement comme dans l'énoncé. La virgule est une virgule décimale (4,8 = quatre virgule huit). 4/5 se lit « quatre cinquièmes », 10⁻³ « dix puissance moins trois », R³ « R au cube ».
- Demande toujours l'UNITÉ : longueur (cm), aire (cm²), volume (cm³) sont trois choses différentes.
- FIGURE (ci-contre, ci-dessous, courbe, diagramme, schéma) : tu ne la vois que si une image t'est donnée. Sinon N'INVENTE AUCUNE valeur : demande à l'élève d'entourer la figure dans le document, ou de te dire les nombres qu'il y lit. Quand tu reçois l'image : dis en une phrase ce que tu lis (noms, valeurs) et demande à l'élève de CONFIRMER avant d'aller plus loin ; sur une courbe, c'est l'élève qui lit la valeur (« Où est 3,6 sur l'axe horizontal ? »).
- Une question « Calculer… » n'est pas une lecture : ne la transforme jamais en « Quel nombre… a… ? ». Si le tableau ou l'énoncé ne donne pas la valeur (case « ? »), dis que ce nombre n'est pas écrit et qu'on va le calculer, puis demande quelles données sont utiles. Si l'élève dit « on ne sait pas » devant cette case, il a raison : dis-le.
- Reprends les groupes de mots de l'énoncé sans les raccourcir : « le nombre de médailles d'or », jamais « le nombre d'or » (c'est une autre notion en mathématiques).
- Ne demande pas le sens d'un mot de consigne (calculer, montrer…) si l'élève ne bloque pas dessus.
- Si le sujet dit « calculatrice interdite », ne la propose jamais.`, infer: 'En mathématiques, la question porte sur l\'énoncé : quelle donnée est utile ? quelle opération est demandée ? Ne calcule jamais à la place de l\'élève.', hint: 'question sur l\'énoncé (donnée utile, opération demandée), sans calcul ni résultat' },
  sciences: { nom: 'sciences (SVT, physique-chimie, technologie)', guide: 'Aide à lire la consigne, le schéma et le protocole. Explique les mots scientifiques avec un exemple de la vie courante. Suis la démarche : observation → hypothèse → conclusion.', infer: 'En sciences, la déduction va de l\'observation à la conclusion (« on voit que… donc… »).', hint: 'conclusion déduite d\'une observation du texte (« on voit que… donc… »)' },
  emc: { nom: 'enseignement moral et civique', guide: 'Explique les mots (droit, devoir, règle, égalité…) avec des exemples simples de la vie de l\'école. Reste neutre : aucun jugement sur des opinions politiques ou religieuses.', infer: 'En EMC, la déduction porte sur la règle, le droit ou le devoir qui s\'applique dans la situation.', hint: 'règle, droit ou devoir qui s\'applique dans la situation, déduit d\'un indice' },
  autre: { nom: 'autre matière', guide: 'Adapte ton aide au document : consigne, vocabulaire, repérage des informations.', infer: 'La déduction doit s\'appuyer sur des indices du document.', hint: 'déduction appuyée sur un indice du texte' }
};
// ---------- Deux types de documents : une activité scolaire (avec consigne) ou une ressource à lire (sans consigne) ----------
const MODES = {
  activite: {
    intro: "Il fait une activité scolaire (consigne, questions) dont les passages numérotés te sont donnés.",
    regles: `DEUX SORTES DE MESSAGES DE L'ÉLÈVE :
- [RÉPONSE] : il répond à ta dernière question ou essaie de faire la consigne. Évalue sa réponse par rapport à CETTE question ou consigne : dis d'abord ce qui est juste, corrige UNE erreur à la fois, ne donne jamais la solution, puis demande l'élément suivant.
- [QUESTION] ou message sans étiquette : il demande de l'aide pour comprendre (mot, phrase, consigne, contexte). Réponds d'abord à sa question, puis ramène-le doucement à l'activité.
TES QUESTIONS viennent de l'activité : ses questions et consignes, dans l'ordre (1, 2, 3…), ou de petites étapes pour y arriver. N'invente JAMAIS une autre question sur le document (par exemple un classement, une comparaison que l'activité ne demande pas).
- Si l'élève dit qu'il a déjà fait une question, crois-le : demande-lui sa réponse pour la vérifier, ou passe à la question suivante de l'activité.
- Quand sa réponse est juste, dis-le clairement, puis passe à la question suivante de l'activité. Une réponse seulement proche (« compter » pour « calculer ») : dis ce qui est juste, puis précise.`
  },
  ressource: {
    intro: "Le document est une RESSOURCE à lire et à comprendre (texte, document, leçon). Il ne contient ni consigne ni exercice : n'en invente jamais et ne parle jamais de « la consigne » ni de « l'exercice ».",
    regles: `TON RÔLE : répondre à la demande de l'élève, rien de plus. Il lit à son rythme et c'est LUI qui choisit ce qu'il veut comprendre (mot, phrase, zone, question). Explique le vocabulaire, aide à reformuler.
- Tu ne poses PAS de question de lecture de ta propre initiative, tu ne proposes pas « de continuer la lecture » et tu ne demandes pas « Tu veux surligner autre chose ? » : après ton explication, tu t'arrêtes (si tu veux inviter, écris une phrase affirmative et variée — « Surligne autre chose si tu veux. », « Tu peux choisir un autre mot. », « Je suis là pour la suite. » — ou n'invite pas).
- Si le passage choisi par l'élève fait plus de 8 mots, ne le recopie pas en entier : va directement à l'explication (le mot ou l'idée difficile).
- Après avoir expliqué une QUESTION ou une consigne de l'exercice, la suite logique est d'essayer : termine en l'invitant à écrire sa réponse (« À toi d'essayer : écris ta réponse, on la vérifie ensemble. »). Après un mot ou une phrase du texte, invite-le à surligner autre chose, ou n'ajoute rien.
- Pas d'amorce de phrase (« Je pense que… ») : l'élève ne répond pas, il surligne. Ta réponse se termine par une phrase complète, jamais par des points de suspension.
- Exception : si l'élève demande qu'on l'interroge (« Pose-moi une question plus facile », « Je ne sais pas »), pose UNE question simple sur l'endroit qu'il vient de travailler. Jamais une question inventée sur le document (classement, comparaison) ni une question de l'exercice qu'il n'a pas choisie.
- Si l'élève répond « oui », « ok » ou « merci » sans rien demander : ne change PAS de sujet et ne pose aucune question sur le texte ; invite-le à surligner un mot ou une phrase, ou à écrire sa question.
DEUX SORTES DE MESSAGES DE L'ÉLÈVE :
- [RÉPONSE] : seulement si tu lui as posé une question juste avant : évalue-le d'après le texte (le juste d'abord, puis UNE précision). Sinon, traite le message comme une demande.
- [QUESTION] ou message sans étiquette : il demande de l'aide (mot, phrase, contexte). Réponds d'abord à sa question, puis arrête-toi.`
  }
};
const modeOf = x => (x === 'ressource' ? 'ressource' : 'activite');
// Reconnaît une activité : une consigne ou une question numérotée, courte, en début de passage
const CONSIGNE = /^(\d+\s*[.)\-:]|exercice|consigne|activité|questions?\b|lis|lisez|réponds|répondez|complète|complétez|relie|reliez|explique|expliquez|décris|décrivez|compare|comparez|calcule|calculez|justifie|justifiez|cite|citez|souligne|soulignez|recopie|recopiez|écris|écrivez|raconte|identifie|observe|observez|indique|indiquez|trouve|trouvez|présente|présentez|rédige|rédigez|coche|cochez|entoure|entourez|classe|classez|associe|associez|qu['’]|que |quel|quelle|quels|quelles|pourquoi|comment|où|qui |quand|combien)/i;
function detectMode(passages) {
  const n = passages.filter(p => p.type !== 'titre' && p.t.length <= 240 && CONSIGNE.test(p.t.trim())).length;
  return n >= 1 ? 'activite' : 'ressource';
}
// Découpe le document en parties (une idée à la fois) : chaque titre ouvre une partie ; les parties trop courtes sont fusionnées
function sectionsOf(passages) {
  const len = s => s.ids.reduce((n, id) => n + ((passages.find(p => p.id === id) || {}).t || '').length, 0);
  const secs = []; let cur = null;
  for (const p of passages) {
    if (p.type === 'titre' || !cur) { cur = { t: p.type === 'titre' ? p.t : '', ids: [] }; secs.push(cur); }
    cur.ids.push(p.id);
  }
  const out = [];
  for (const s of secs) { if (out.length && len(s) < 140) out[out.length - 1].ids.push(...s.ids); else out.push(s); }
  if (out.length > 1 && len(out[0]) < 140) { out[1].ids = out[0].ids.concat(out[1].ids); out[1].t = out[1].t || out[0].t; out.shift(); }
  return out.length >= 3 ? out.map(s => ({ t: s.t.slice(0, 80), ids: s.ids })) : [];
}
const scopeLine = ids => { const a = (Array.isArray(ids) ? ids : []).map(Number).filter(Number.isInteger).slice(0, 40);
  return a.length ? `\n\nPARTIE EN COURS : l'élève travaille seulement sur les passages ${a.join(', ')}. Pose tes questions et choisis tes indices dans cette partie ; ne parle pas des autres parties sauf si l'élève le demande.` : ''; };
const subj = x => (SUBJECTS[x] ? x : 'auto');

// Vérifie qu'un texte respecte le profil du niveau (longueur, nombre de phrases, constructions écartées)
function levelIssues(text, level, extra = 0) {
  const L = lv(level), out = [];
  const t = String(text || '').replace(/[«“"][^»”"]*[»”"]/g, ' citation ');
  const sentences = t.split(/(?<=[.!?…])\s+/).map(x => x.trim()).filter(x => words(x) >= 5); // « C'est normal de bloquer. » : une phrase d'encouragement ne compte pas
  const long = sentences.find(x => words(x) > L.maxWords + 2);
  if (long) out.push(`une phrase est trop longue (${L.maxWords} mots maximum)`);
  const maxS = extra ? L.longSentences : L.maxSentences;
  if (sentences.length > maxS + 1) out.push(`trop de phrases (${maxS} maximum)`);
  const b = t.match(L.banned);
  if (b) out.push(`construction trop difficile pour ${level} : « ${b[0]} »`);
  return out;
}
function levelCheck(text, level, extra = 0) {
  const t = String(text || '').replace(/[«“"][^»”"]*[»”"]/g, ' citation ');
  const ss = t.split(/(?<=[.!?…])\s+/).map(x => x.trim()).filter(x => words(x) >= 1);
  return { niveau: level, phrases: ss.length, max_mots: ss.reduce((m, x) => Math.max(m, words(x)), 0), problemes: levelIssues(text, level, extra) };
}
const problems = (r, level, extra = 0) => {
  const out = [];
  if (CLOSED.test(r.fr || '')) out.push("question fermée interdite (« tu comprends ? ») : pose une tâche qui oblige l'élève à produire un mot ou une phrase");
  return out.concat(levelIssues(r.fr, level, extra));
};
// Si le modèle écrit hors niveau ou pose une question fermée, on lui demande une seule fois de corriger
async function short(r, msgs, model = ALBERT_MODEL, level = 'A2+', extra = 0) {
  const issues = problems(r, level, extra);
  if (!issues.length) return r;
  const L = lv(level);
  const consigne = `Réécris ta réponse précédente SANS changer son contenu pour l'élève (même explication, même mot, même question) : ${issues.join(' ; ')}. ${extra ? L.longSentences : L.maxSentences} phrases courtes au maximum (${L.maxWords} mots maximum chacune), niveau ${level}, une seule question au maximum, sans salutation. Ne réponds pas à cette consigne et n'écris aucune formule comme « c'est compris » ou « d'accord ». Même format JSON.`;
  const again = parseJson(await albert([...msgs, { role: 'assistant', content: JSON.stringify(r) }, { role: 'user', content: consigne }], { model }));
  if (derailed(r, again, true)) return r;
  const better = problems(again, level, extra).length < issues.length || (CLOSED.test(r.fr || '') && !CLOSED.test(again.fr || ''));
  if (!better) return r;
  again.corrige = true;
  if (r.titre) again.titre = r.titre;
  if (r.matiere) again.matiere = r.matiere;
  return again;
}

const hasQ = t => /[?؟]/.test(t || '');
// Une question du tuteur doit avoir sa réponse dans le texte : on exige une preuve citée exactement (un seul nouvel essai)
// Une relance ne doit jamais remplacer la vraie réponse par un accusé de réception de la consigne (« C'est compris… ») ou une réponse hors sujet
const META_RE = /^\s*(?:c['’]est (?:compris|noté)|d['’]accord|compris\b|entendu|très bien, je)|vérifier les preuves|preuves? (?:exacte|du texte|dans le texte)|je vais (?:toujours|bien|être|utiliser)\b/i;
function derailed(orig, again, strict) {
  const a = String(again && again.fr || '');
  if (!a.trim() || META_RE.test(a)) return true;
  if (!strict) return false;
  const o = content(orig && orig.fr), t = new Set(content(a));
  return o.length >= 3 && o.filter(x => t.has(x)).length / o.length < 0.2; // le contenu a changé : on garde l'original
}
const isHelp = msgs => /^\[(?:SÉLECTION|QUESTION|INDICE)/.test(String(([...msgs].reverse().find(m => m.role === 'user') || {}).content || ''));
async function grounded(r, msgs, model, level, passages) {
  if (!hasQ(r.fr) || r.hors || !passages.length) return r;
  if (isHelp(msgs)) return r; // une explication demandée par l'élève n'est jamais réécrite
  if (r.preuve && findQuote(passages, r.preuve)) return r;
  const again = parseJson(await albert([...msgs, { role: 'assistant', content: JSON.stringify(r) }, { role: 'user', content: "Reprends ta réponse précédente pour l'élève, avec le même contenu, et vérifie que le texte donne la réponse à ta question ou permet de la déduire. Donne dans \"attendu\" la réponse attendue et dans \"preuve\" une citation EXACTE du texte (10 mots maximum) qui la justifie. Si le texte ne contient pas cette information, pose une autre question qui s'appuie sur un indice du texte. Ne réponds pas à cette consigne et n'écris aucune formule comme « c'est compris » : écris directement ton message à l'élève. Même format JSON, mêmes limites de longueur." }], { model }));
  if (!derailed(r, again, false) && again.preuve && findQuote(passages, again.preuve) && problems(again, level).length <= problems(r, level).length) {
    if (r.titre) again.titre = r.titre; if (r.matiere) again.matiere = r.matiere;
    return again;
  }
  return r;
}
const label = p => `[${p.id}]${p.type === 'titre' ? ' (titre)' : ''} ${p.t}`;

function system(l1, level, subject = 'auto', mode = 'activite') {
  const L = LEVELS[level] || LEVELS['A2+'], S = SUBJECTS[subject] || SUBJECTS.auto, M = MODES[modeOf(mode)];
  return `Tu es un tuteur bienveillant pour un élève allophone (niveau ${level} du CECRL, en français scolaire). Sa langue première : ${LANGS[l1]}.\nPOSTURE : tu es comme un enseignant assis à côté de l'élève. Tu parles avec chaleur et naturel : tu reprends ce qu'il vient de dire (« Tu trouves 24 : … »), tu varies tes phrases (jamais deux fois la même), tu encourages ses efforts avec des mots sincères. Tu ne refuses jamais sèchement : tu n'écris jamais « je ne peux pas », « je n'ai pas le droit » ni « je suis ton tuteur ». Quand l'élève demande la réponse ou bloque, tu proposes de chercher ensemble et tu donnes une vraie aide, de plus en plus concrète (consigne AIDE GRADUÉE quand elle t'est donnée).\nCOMME UN VRAI TUTEUR : écoute d'abord, puis réagis à ce qu'il a VRAIMENT dit, avec ses mots. Petites transitions naturelles et variées (« D'accord. », « Bonne question ! », « Voyons ensemble. »), jamais la même formule deux fois de suite. Quand il se trompe, ne dis pas « faux » : montre d'abord ce qui est juste dans son idée, puis guide par une question (« Tu as bien pris les boules bleues. Et le total ? »). Quand il réussit, dis précisément ce qu'il a bien fait (« Tu as bien lu la colonne Or. ») : tu félicites l'effort et la méthode, jamais l'intelligence (pas de « tu es fort », « tu es doué »). S'il dit une émotion (« c'est dur », « j'en ai marre »), reconnais-la d'abord, en une phrase, puis propose une toute petite étape. Une seule question à la fois. Sa langue première est une ressource : il peut réfléchir ou répondre dans sa langue, et tu l'en félicites.\nMATIÈRE : ${S.nom}. ${S.guide}\n\nNIVEAU ${level} (CECRL) — ta façon d'écrire :\n${L.profil}\n${subject === 'maths' ? L.diffMaths : L.diff}\n- Si le niveau a changé depuis tes messages précédents, ne copie PAS leur style : écris au niveau ${level} actuel.
${M.intro} Appuie-toi d'abord sur les passages. L'élève peut aussi poser des questions plus générales sur le thème ou la matière (personnages, lieux, mots, contexte) : réponds-y avec des connaissances générales SÛRES, en 2 phrases courtes, et ajoute "hors": true. Si tu n'es pas certain d'un fait, dis-le (« Je ne suis pas sûr : demande à ton professeur »). Si la question n'a aucun rapport avec l'activité ou la matière, ou si elle est inappropriée, refuse gentiment et ramène l'élève à l'activité.

CHARGE COGNITIVE : l'élève est vite saturé. Chaque réponse doit être COURTE.
- "fr" : ${L.maxSentences} phrases maximum (plus, si tu veux, une phrase très courte d'encouragement), ${L.maxWords} mots maximum par phrase, une seule idée, UNE seule question à la fois. Jamais de liste, jamais de paragraphe. Exception : pour un exemple résolu, un rappel de règle, un petit test ou une correction, jusqu'à ${L.longSentences} phrases courtes, une étape par phrase.
- "mots" : ${L.maxMots} mots maximum, seulement ceux sans lesquels l'élève ne peut pas répondre, recopiés exactement comme ils apparaissent dans "fr".
- "l1" : ${NOL1(l1) ? 'toujours une chaîne vide "" (l\'élève n\'a pas encore choisi de langue d\'appui : tout se fait en français)' : `traduction fidèle de "fr" en ${LANGS[l1]} (même longueur, rien en plus)`}.
- Respecte strictement le NIVEAU ${level} ci-dessus.

PÉDAGOGIE :
- Ne donne pas la réponse de l'exercice d'emblée : guide par une question, un indice, une reformulation, un exemple semblable. Attends la réponse de l'élève avant d'expliquer. Quand une consigne AIDE GRADUÉE t'est donnée, suis-la exactement.
- Si l'élève dit qu'il n'a pas compris : NE lui redemande PAS s'il comprend. Simplifie vraiment : découpe la phrase difficile en 2 phrases très courtes avec des mots plus simples, mets 1 ou 2 mots difficiles dans "mots" (obligatoire dans ce cas), puis termine par une petite tâche.
- INTERDIT : les questions fermées comme « Tu comprends ? », « Est-ce que c'est clair ? », « As-tu compris ? » (l'élève répond oui par réflexe). Pose plutôt une tâche qui l'oblige à produire quelque chose : choisir un mot, dire une idée dans sa langue, compléter une phrase (« Athènes est une… »), retrouver un mot dans le passage.
- Si l'élève demande un indice : donne un seul petit indice, pas la solution.
- Pour répondre : l'élève dit d'abord son idée dans sa langue ou en français approximatif, puis tu l'aides avec une amorce (« Je pense que… parce que… »), puis il reformule seul. Corrige une erreur à la fois, avec douceur.
- Le niveau (${level}) est réglé par l'enseignant dans le menu « Niveau » : si l'élève te parle de niveau, dis simplement « Je m'adapte à ton niveau. » puis : s'il y a une question en attente, repose-la ; sinon invite-le à surligner un mot ou une phrase pour avoir de l'aide. Ne pose PAS de question oui/non (« Veux-tu continuer ? »).
- ${NOL1(l1) ? "Si l'élève écrit dans une autre langue, comprends-le et réponds en français simple." : `Si l'élève écrit en ${LANGS[l1]}, comprends-le et réponds comme prévu.`}
- Encourage avec des mots variés et sincères (une phrase courte au plus), surtout quand l'élève bloque ou se trompe.
- L'élève ne voit PAS les numéros de passage : n'écris JAMAIS « passage 3 ». Pour montrer un endroit du document, cite ses premiers mots entre « » (8 mots maximum) ou dis où regarder (« la question en haut », « l'encadré Vocabulaire »), et mets le numéro dans "refs". Ne mentionne jamais les noms techniques du format (refs, mots, JSON).
- SUIVI : relis ta dernière question. Évalue la réponse de l'élève par rapport à CETTE question, pas à une autre. Si elle est juste ou en partie juste, dis-le d'abord (« Oui, … ») puis fais avancer. N'écris « Mais regarde bien… » que si la réponse est fausse, et donne alors un seul indice. Ne change pas de mot ni de sujet tant que ta question n'a pas reçu de réponse : si l'élève ne répond pas, reprends la même question plus simplement.
- Ne dis JAMAIS « Dis-moi ton idée » ni « Je vais t'aider après » sans question précise : chaque fois que tu attends une réponse de l'élève, la question est posée dans le même message.

${M.regles}

QUESTIONS : avant de poser une question, décide la réponse attendue ("attendu") et la citation EXACTE du texte qui la justifie ("preuve", 10 mots maximum). Si le texte ne donne pas l'information, ne pose pas cette question. Évalue la réponse de l'élève par rapport à "attendu" de ta DERNIÈRE question. Si l'élève remarque qu'une information manque dans le texte et que c'est vrai, dis-lui qu'il a raison. Après une demande d'aide, reprends la même question (plus simple) ou pose une petite tâche qui y mène : ne l'abandonne pas.
PROGRESSION : repérer (qui ? où ? quand ?) → vocabulaire en contexte → déduire (pourquoi ? comment le sais-tu ?) → redire avec ses mots. Monte d'un cran après une bonne réponse ; redescends d'un cran après deux échecs.
- [TRAVAIL] : l'élève te montre ce qu'il a écrit (sa production ou sa synthèse). Dis d'abord ce qui est réussi (une chose précise), puis UNE seule amélioration (un mot, une forme, une idée qui manque) avec une amorce. Ne réécris jamais son texte à sa place et ne donne jamais la version corrigée complète.
- [PARTIE SUIVANTE] : l'élève passe à la partie suivante (voir « PARTIE EN COURS »). Dis en une phrase de quoi elle parle, puis pose UNE question concrète de repérage.
- [FIN DU DOCUMENT] : toutes les parties ont été vues. S'il y a une question-titre (problématique), propose à l'élève d'y répondre en 2 ou 3 phrases avec « parce que… » (dans « Mon travail » s'il fait une activité, sinon dans la conversation). Sinon propose-lui de dire en 2 phrases ce qu'il a retenu.
${NOL1(l1) ? '' : `- Si tu n'es pas sûr d'un terme en ${LANGS[l1]}, garde le mot français entre guillemets plutôt que d'inventer.`}

QUESTIONS DE COMPRÉHENSION : ${S.infer} Alterne les questions littérales (« Qui ? Où ? Quand ? ») et les questions d'INFÉRENCE (« Comment le sais-tu ? Que ressent… ? Pourquoi, à ton avis ? »), où la réponse se déduit d'indices du texte. Pour une inférence, demande à l'élève de SURLIGNER l'indice dans le document, puis de dire sa déduction avec « Je pense que… parce que le texte dit… ».
- Si le message commence par [INDICE] : l'élève montre l'extrait qui justifie sa réponse. Dis si c'est un bon indice (d'abord ce qui est juste), puis demande-lui ce qu'on en déduit avec « Je pense que… parce que… », sans donner la réponse.

DEMANDE D'AIDE SUR UNE SÉLECTION : si le message de l'élève commence par [SÉLECTION], l'élève a surligné ou entouré ce texte pour le comprendre : explique EXACTEMENT ce qui est entre les premiers « », commence par le répéter (« aminci » veut dire…) et n'explique JAMAIS un autre mot ou groupe de mots de la phrase voisine. La phrase donnée après « dans la phrase : » sert seulement à choisir le bon sens du mot. Explique d'abord brièvement, avec des mots plus simples et une image concrète tirée du texte (pour un sens figuré : dis ce que l'on voit, par ex. « tacher le ciel : le ciel est noir, il n'y a pas un arbre »), jamais deux synonymes vagues. Si ta dernière question à l'élève est restée sans réponse, termine par une phrase qui la lui repose (« Maintenant, reviens à la question : … »).
- Explique-le en français simple : ${L.maxSentences} phrases maximum, ${L.maxWords} mots maximum par phrase. Mets les mots difficiles dans "mots" (${L.maxMots} maximum). Si c'est un seul mot, donne son sens avec un mini-exemple.
- Si le message commence par [SÉLECTION image] : lis la zone entourée sur l'image et explique-la de la même façon.
- Si la sélection est la consigne ou une question de l'exercice : reformule-la plus simplement, SANS y répondre.
- Ne donne pas la réponse de l'exercice. Termine par une phrase courte et naturelle (« Surligne autre chose si tu veux. ») ou par une petite tâche.
- [MODE: français + langue] : même explication ; "l1" est sa traduction et sera affichée tout de suite.

QUESTION LIBRE DE L'ÉLÈVE : il peut te poser une question, en français ou dans sa langue (parfois suivie de « (à propos de : « … ») » : c'est le texte qu'il a surligné).
- Réponds d'abord à SA question, en français simple (${L.maxSentences} phrases maximum), avant toute nouvelle question de ta part.
- S'il te demande la réponse de l'exercice, ne refuse pas : propose de la trouver ensemble et suis l'AIDE GRADUÉE (indice, exemple semblable, première étape ensemble).
- S'il a écrit dans sa langue, remplis "dire" avec sa question dite en français simple (une phrase, niveau ${level}) pour qu'il puisse la répéter. Sinon, n'ajoute pas "dire".
- Distingue sa question d'une réponse à ta question : si c'est une réponse, évalue-la comme prévu.

POINTS RAPIDES : l'application peut poser à l'élève une question de bilan ; sa réponse t'arrive sous forme de message.
- [POINT confiance] avec 😕 « Pas encore » : simplifie, donne un mini-exemple, mets 1 mot dans "mots", puis une petite tâche. Avec 🙂 « Un peu » : félicite en 3 mots et demande-lui de redire l'idée avec ses mots. Avec 😀 « Oui » : félicite et propose l'étape suivante de l'activité, sans donner la réponse.
- [POINT reformuler] : l'élève a redit l'idée avec ses mots (peut-être dans sa langue). Dis d'abord ce qui est juste, puis UNE seule amélioration (un mot ou une phrase en français), puis propose de la redire en français avec une amorce.
- Une ligne [POINT qcm] ou [POINT inference] avant son message : tiens-en compte. S'il s'est trompé, reformule plus simplement. Si l'indice n'a pas été trouvé, aide-le à le repérer (« Qu'est-ce qui montre qu'il fait froid ? ») sans le donner. S'il a trouvé, félicite en 3 mots et demande-lui de redire la déduction avec « parce que… ».

Exemple après « je n'ai pas compris » : {"fr": "Athènes est une cité. Elle a une démocratie. Que veut dire « démocratie » pour toi ?", "l1": "(traduction fidèle de fr)", "refs": [5], "mots": [{"fr": "démocratie", "l1": "(équivalent)"}]}
Exemple de réponse correcte : {"fr": "Regarde « Comment la cité d'Athènes… ». Que veut dire « cité » ?", "l1": "(traduction fidèle de fr)", "refs": [5], "mots": [{"fr": "cité", "l1": "(équivalent)"}]}

Réponds UNIQUEMENT par un objet JSON : {"fr": string, "l1": string, "refs": [numéros de passages], "attendu": string (réponse attendue à ta question, si tu en poses une), "preuve": string (citation exacte du texte qui la justifie, 10 mots maximum), "mots": [{"fr": string, "l1": string}], "dire": string (facultatif), "hors": true (facultatif : seulement si ta réponse utilise une connaissance générale absente du document)}`;
}


const VERSION = '2.4.2';
app.get('/api/health', (_q, res) => res.json({ version: VERSION, model: ALBERT_MODEL, code: !!ACCESS_CODE }));

// Diagnostic (enseignant) : /api/diag?code=VOTRE_CODE — teste la clé sur chaque modèle d'Albert et montre la réponse exacte d'Albert
app.get('/api/diag', async (_req, res) => {
  const out = { version: VERSION, modele_configure: ALBERT_MODEL, modele_images: ALBERT_VISION_MODEL, base: ALBERT_BASE_URL, modeles: [], tests: [] };
  const H = { 'Content-Type': 'application/json', Authorization: `Bearer ${ALBERT_API_KEY}` };
  try {
    const r = await fetch(`${ALBERT_BASE_URL}/models`, { headers: H });
    const j = await r.json().catch(() => null);
    out.liste_modeles = r.status;
    out.modeles = j && Array.isArray(j.data) ? j.data.map(m => ({ id: m.id, type: m.type || m.object || '' })) : [];
  } catch (e) { out.liste_modeles = 'erreur : ' + e.message; }
  const ids = [...new Set([ALBERT_MODEL, ALBERT_VISION_MODEL, ...out.modeles.filter(m => !/embed|rerank|whisper|audio|ocr/i.test(m.id + ' ' + m.type)).map(m => m.id)])].filter(Boolean).slice(0, 8);
  for (const id of ids) {
    const t0 = Date.now();
    try {
      const r = await fetch(`${ALBERT_BASE_URL}/chat/completions`, { method: 'POST', headers: H, body: JSON.stringify({ model: id, messages: [{ role: 'user', content: 'Réponds seulement : OK' }], max_tokens: 5 }) });
      const txt = await r.text();
      out.tests.push({ modele: id, statut: r.status, ok: r.ok, ms: Date.now() - t0, reponse: txt.slice(0, 300) });
    } catch (e) { out.tests.push({ modele: id, statut: 'erreur', ok: false, reponse: e.message }); }
  }
  res.json(out);
});
app.get('/api/models', async (_req, res) => {
  try {
    const r = await fetch(`${ALBERT_BASE_URL}/models`, { headers: { Authorization: `Bearer ${ALBERT_API_KEY}` } });
    res.json(await r.json());
  } catch (e) { res.status(500).json({ error: e.message }); }
});

app.post('/api/analyze', upload.single('file'), async (req, res) => {
  try {
    const f = req.file; if (!f) return res.status(400).json({ error: 'Aucun fichier reçu.' });
    const l1 = LANGS[req.body.l1] ? req.body.l1 : 'fr';
    const level = LEVELS[req.body.level] ? req.body.level : 'A2+';
    const subject = subj(req.body.subject);
    const name = f.originalname || '';
    let text = '', kind = 'text';
    if (f.mimetype === 'application/pdf') {
      text = (await pdf(f.buffer)).text; kind = 'pdf';
      // Document de mathématiques : relecture avec fractions et exposants (pdf-parse les perd) ; sinon on garde l'extraction d'origine
      const mathy = req.body.subject === 'maths' || (text.match(/\b(calculer|montrer que|d[ée]terminer|[ée]quation|fraction|triangle|p[ée]rim[èe]tre|aire|pourcentage|cosinus|th[ée]or[èe]me|exercice \d|probabilit[ée])\b/gi) || []).length >= 4;
      if (mathy) {
        try { const t2 = await pdfTextMath(f.buffer); if (t2 && t2.replace(/\s/g, '').length >= 0.6 * text.replace(/\s/g, '').length) text = t2; }
        catch (e) { console.warn('Lecture mathématique impossible, extraction standard conservée :', e.message); }
      }
    }
    else if (/wordprocessingml|\.docx$/i.test(f.mimetype + name)) { text = (await mammoth.extractRawText({ buffer: f.buffer })).value; kind = 'docx'; }
    else if (f.mimetype.startsWith('image/')) {
      kind = 'image';
      if (!ALBERT_VISION_MODEL) return res.status(400).json({ error: "Aucun modèle d'image configuré (ALBERT_VISION_MODEL). Utilise un PDF ou un Word." });
      const url = `data:${f.mimetype};base64,${f.buffer.toString('base64')}`;
      const out = await albert([{ role: 'user', content: [
        { type: 'text', text: 'Transcris fidèlement tout le texte de ce document scolaire (consignes, textes, questions, légendes des schémas). Réponds en JSON : {"texte": "..."} avec un retour à la ligne entre les blocs.' },
        { type: 'image_url', image_url: { url } }] }], { model: ALBERT_VISION_MODEL });
      text = parseJson(out).texte || '';
    } else if (f.mimetype.startsWith('text/')) text = f.buffer.toString('utf8');
    else return res.status(400).json({ error: 'Format non pris en charge (PDF, Word .docx, image).' });

    const hadVideo = /<iframe/i.test(text);
    text = text.replace(/<iframe[\s\S]*?<\/iframe>/gi, ' ');
    const passages = toPassages(text);
    if (!passages.length && hadVideo) return res.status(422).json({ error: "Ce document ne contient qu'une vidéo intégrée (code « iframe »). Je ne peux pas lire une vidéo : ajoute sa transcription ou un texte." });
    if (!passages.length) return res.status(422).json({ error: "Aucun texte lisible. Si c'est un scan, envoie-le comme image." });

    const suggere = detectMode(passages), sections = sectionsOf(passages);
    const mode = req.body.mode === 'ressource' || req.body.mode === 'activite' ? req.body.mode : suggere;
    const doc = passages.map(label).join('\n');
    // Maths, « Faire mon activité » : le tuteur commence par la fiche de la première question
    let track0 = null, firstNote = '';
    if (subject === 'maths' && mode === 'activite') {
      const fq = firstQuestion(passages), dt = passages.map(p => p.t).join('\n');
      const p = fq && dt.length < 60000 ? await getPlan(fq.text, dt, '', null) : null;
      if (p) {
        track0 = { key: fq.key, text: fq.text, label: fq.label, step: 0, tries: 0, helps: 0, fig: '', done: false };
        firstNote = planTurn({ plan: p, track: track0, kind: p.figure ? 'figure-ask' : 'new', lu: '', intent: null, help: 1, correction: false, mode, justifier: true }).note;
      }
    }
    const detect = subject === 'auto' ? ` Ajoute aussi un champ "matiere" : l'un de ces mots exactement : histoire, geographie, francais, maths, sciences, emc, autre.` : '';
    const m0 = [
      { role: 'system', content: system(l1, level, subject, mode) + scopeLine(sections[0] && sections[0].ids) },
      { role: 'user', content: `${mode === 'activite' ? "Voici l'activité de l'élève" : 'Voici le document que l\'élève doit lire (aucune consigne)'} :\n${doc}\n\n${firstNote ? `Premier message, TRÈS court (l'accueil est déjà fait : ne dis pas bonjour). ${firstNote.replace('choisie par l\'élève', 'par laquelle on commence')}` : mode === 'activite' ? 'Premier message, TRÈS court (l\'accueil est déjà fait : ne dis pas bonjour) : une phrase chaleureuse qui dit de quoi parle l\'activité (numéro du passage de la consigne dans "refs"), puis UNE question simple pour commencer, qui mène à la première question de l\'activité.' : 'Réponds seulement avec le JSON : "fr" = une seule phrase très courte qui dit de quoi parle le texte, SANS question ; "l1" = sa traduction (chaîne vide si aucune langue d\'appui). N\'invente aucune consigne.'} Ajoute dans le JSON un champ "titre" (titre court de l'activité).${detect}` }];
    let first = await short(parseJson(await albert(m0)), m0, ALBERT_MODEL, level);
    if (!firstNote) first = await grounded(first, m0, ALBERT_MODEL, level, passages); // avec une fiche, la première question est celle de l'étape 1
    let detected = subject;
    if (subject === 'auto') { const m = normTxt(first.matiere); detected = SUBJECTS[m] && m !== 'auto' ? m : 'auto'; }
    delete first.matiere;
    res.json({ kind, passages, first, title: first.titre || name, subject: detected, mode, suggere, sections, track: track0 });
  } catch (e) { console.error(e); res.status(500).json({ error: e.message }); }
});

// Demande [SÉLECTION] : la réponse doit parler du mot ou du groupe choisi, pas d'un mot voisin
async function onSelection(r, msgs, model, level, image) {
  const last = String(([...msgs].reverse().find(m => m.role === 'user') || {}).content || '');
  if (image || !/^\[SÉLECTION\]/.test(last)) return r;
  const m = last.match(/«\s*([^»]+?)\s*»/); if (!m) return r;
  const sel = m[1], toks = content(sel);
  if (!toks.length || toks.length > 3) return r;
  const stems = toks.map(t => t.slice(0, 5));
  const mentions = x => { const w = new Set(tokens(x).map(t => t.slice(0, 5))); return stems.some(s => w.has(s)); };
  const text = (x) => `${x.fr || ''} ${(Array.isArray(x.mots) ? x.mots : []).map(q => q && q.fr).join(' ')}`;
  if (mentions(text(r))) return r;
  const again = parseJson(await albert([...msgs, { role: 'assistant', content: JSON.stringify(r) }, { role: 'user', content: `Ta réponse ne parle pas de « ${sel} ». Explique EXACTEMENT « ${sel} » (pas un mot voisin de la phrase), en commençant par ce mot, au niveau ${level}. Ne réponds pas à cette consigne et n'écris aucune formule comme « c'est compris » : écris directement ton explication. Même format JSON.` }], { model }));
  if (derailed(r, again, false) || !mentions(text(again)) || problems(again, level).length > problems(r, level).length) return r;
  if (r.titre) again.titre = r.titre;
  return again;
}

// Parcours « Comprendre » : le tuteur répond à la demande, il ne relance pas la lecture
// Résultat annoncé seul (« Je trouve 4/20 », « B », « 12 cm ») : en maths le tuteur ne peut pas le vérifier, donc la réponse est la même, juste ou faux
const BARE_RESULT = /^(?:je (?:trouve|pense(?: que c['’]est)?|crois(?: que c['’]est)?|choisis|dis)|j['’]ai trouvé|(?:le |mon )?r[ée]sultat(?: est)?|(?:la |ma )?r[ée]ponse(?: est)?|c['’]est|[çc]a (?:fait|donne)|=)?\s*[:=]?\s*(?:[−–-]?\s?\d+(?:[.,]\d+)?(?:\s?\/\s?\d+(?:[.,]\d+)?)?\s?(?:%|cm[²³]?|mm[²³]?|m[²³]?|km|kg|g|°|€)?|[A-D])\s*\.?$/i;
const lastLine = raw => String(raw || '').split('\n').pop().replace(/^\[[^\]]*\]\s*/, '').trim();
const CLOSED_OFFER = /^(?:tu veux|veux-tu|souhaites-tu|tu souhaites|est-ce que tu veux|as-tu besoin|tu as besoin|on continue|on passe|tu es prêt|es-tu prêt|tu peux surligner|veux-tu surligner|tu veux surligner|tu veux voir|tu veux que)/i;
const TRY = ["À toi d'essayer : écris ta réponse, on la vérifie ensemble.", "Essaie quand tu veux : écris ta réponse, je la regarde avec toi.", "À toi de jouer : écris ce que tu trouves, on vérifie ensemble."];
const INVITE_RE = /^(?:surligne|tu peux (?:choisir|surligner)|je suis là|choisis un autre)/i;
const INVITES = ['Surligne autre chose si tu veux.', 'Tu peux choisir un autre mot ou une autre phrase.', 'Je suis là si tu veux continuer.'];
function tidyReply(out, mode, userText, seed = 0, keepOffer = false) {
  if (!out || typeof out.fr !== 'string') return out;
  let fr = out.fr;
  // « Je m'adapte à ton niveau » n'est dit que si l'élève parle de niveau
  if (!/niveau|a2|b1|facile|difficile|simple/i.test(userText || '')) fr = fr.replace(/^\s*Je m['’]adapte à ton niveau\.?\s*/i, '');
  if (mode === 'ressource') {
    fr = fr.replace(/\s*(?:Je pense que|Je crois que|Pour moi|Je vois que|Je comprends que|C['’]est)\s*(?:\.{3}|…)\s*$/i, '').trim(); // amorce laissée en suspens : inutile ici
    fr = fr.replace(/\s*Je (?:pense|crois) que\s*(?:\.{3}|…)(?:\s*parce que\s*(?:\.{3}|…))?\s*/gi, ' ').replace(/\s{2,}/g, ' ').trim(); // « Je pense que… parce que… » : l'élève ne répond pas ici
    const ss = fr.split(/(?<=[.!?])\s+/).filter(Boolean);
    if (ss.length > 1) {
      const last = ss[ss.length - 1];
      if (!keepOffer && /\?\s*$/.test(last) && CLOSED_OFFER.test(last.replace(/^[«"\s]+/, ''))) { ss[ss.length - 1] = INVITES[seed % INVITES.length]; fr = ss.join(' '); }
    }
  }
  return fr === out.fr ? out : { ...out, fr: fr.trim() };
}

// Dernier message du tuteur (objet JSON enregistré par l'interface)
function lastAssistant(history) {
  const la = [...history].reverse().find(m => m.role === 'assistant');
  let o = null; try { o = JSON.parse(la ? la.content : 'null'); } catch {}
  return o && typeof o === 'object' ? o : {};
}
const focusOf = (lastU, repere) => ((String(lastU).match(/\(à propos de : «\s*([\s\S]*?)\s*»/) || [])[1] || repere || '').trim();
const CALC_Q = /calcul|pourcentage|combien de fois|moyenne|total|somme|diff[ée]rence|probabilit|aire|p[ée]rim[eè]tre|volume|vitesse|arrondi|fraction/i;
// Le tuteur demande-t-il de lire un nombre (« Regarde le nombre total… », « Combien de médailles… ? ») plutôt qu'un calcul ?
const isLecture = q => readingAsk(q) || (/\?\s*$/.test(String(q || '').trim()) && !CALC_Q.test(q));
// Le modèle, pour lui seul, dit si la réponse attendue se LIT dans le document (nombre + passage exact) ou se CALCULE (son calcul, avec les nombres de l'énoncé).
// Le serveur ne le croit pas sur parole : le passage doit être dans le document (readingVerdict), le calcul est refait par l'outil (solveVerdict).
async function checkAnswer(q, who, docText) {
  return parseJson(await albert([{ role: 'system', content: 'Tu es professeur de mathématiques. On te donne un document et la dernière demande faite à l\'élève. Pour toi seul (l\'élève ne verra jamais ta réponse) : si la réponse attendue est un nombre écrit tel quel dans le document (lecture d\'un tableau ou de l\'énoncé, sans calcul), réponds {"type": "lecture", "attendu": ce nombre, "preuve": le passage exact du document qui le contient, 10 mots maximum}. Si la réponse attendue est un nombre qui se calcule, réponds {"type": "calcul", "calcul": UNE expression qui donne ce nombre, écrite avec les nombres du document et seulement + - × ÷ / ^ et des parenthèses (pas de lettre, pas de signe =), "resultat": sa valeur}. Si la demande n\'attend pas un nombre, ou si tu n\'es pas sûr, réponds {"type": null}. Réponds UNIQUEMENT par un objet JSON.' }, { role: 'user', content: `Document :\n${docText}\n\n${who} : ${q}` }]));
}
// Une question de l'énoncé a toujours la même réponse : on garde le résultat de la vérification (en mémoire seulement, aucune donnée d'élève)
const CHECKS = new Map();
globalThis.__clearChecks = () => CHECKS.clear(); // pour les tests
async function cachedCheck(q, docText) {
  const k = q.toLowerCase().replace(/\s+/g, ' ').slice(0, 300) + '|' + docText.length;
  if (CHECKS.has(k)) return CHECKS.get(k);
  let g = null; try { g = await checkAnswer(q, "Question de l'exercice", docText); } catch (e) { console.warn('vérification :', e.message); return null; } // un échec (Albert occupé) n'est pas gardé : on réessaiera
  if (CHECKS.size > 300) CHECKS.delete(CHECKS.keys().next().value);
  CHECKS.set(k, g); return g;
}
// La fiche d'une question : préparée une fois (avec l'image de la figure quand l'élève l'a entourée), gardée en mémoire (aucune donnée d'élève)
const PLANS = new Map(), PLAN_FAIL = new Map();   // échec récent : on ne réessaie pas à chaque message (le tuteur resterait lent)
const planKey = (q, fig, docText) => `${qKey(q)}|${qKey(fig).slice(0, 80)}|${docText.length}`;
async function getPlan(qtext, docText, fig = '', image = null) {
  const k = planKey(qtext, image ? '#image' : fig, docText);
  if (PLANS.has(k)) return PLANS.get(k);
  if (Date.now() - (PLAN_FAIL.get(k) || 0) < 60000) return null;
  const user = planUser(qtext, docText, fig);
  const msgs = [{ role: 'system', content: PLAN_SYSTEM }, { role: 'user', content: image ? [{ type: 'text', text: user }, { type: 'image_url', image_url: { url: image } }] : user }];
  let p = null;
  for (let essai = 0; essai < 2 && !p; essai++) {   // une fiche illisible ou incomplète : un second essai (sans fiche, le tuteur accompagne moins bien)
    try { p = checkPlan(parseJson(await albert(msgs, { model: image && ALBERT_VISION_MODEL ? ALBERT_VISION_MODEL : ALBERT_MODEL })), docText, fig); }
    catch (e) { console.warn('fiche :', e.message); if (e instanceof Busy) return null; }
    if (!p) console.warn('fiche refusée' + (essai ? '' : ', nouvel essai'));
  }
  if (!p) { if (PLAN_FAIL.size > 200) PLAN_FAIL.clear(); PLAN_FAIL.set(k, Date.now()); return null; }
  if (PLANS.size > 200) PLANS.delete(PLANS.keys().next().value);
  PLANS.set(k, p);
  if (image && p.figure_lue) PLANS.set(planKey(qtext, p.figure_lue, docText), p); // les messages suivants retrouvent la même fiche
  return p;
}
globalThis.__clearPlans = () => { PLANS.clear(); PLAN_FAIL.clear(); }; // pour les tests
const ANSWERISH = lu => looseValue(lu) !== null || /^(?:c['’]est\s+(?:la\s+)?|je (?:choisis|prends)\s+(?:la\s+)?|(?:la\s+)?r[ée]ponse\s+|la\s+|le\s+)?[A-D]\s*[.!]?$/i.test(lu) || (lu.split(/\s+/).length <= 8 && !/\?\s*$/.test(lu) && !/^(?:que|quoi|qu['’]|comment|pourquoi|c['’]est quoi|est-ce|explique|aide)/i.test(lu));
const FIG_INVITE = /(surlign|entour|encadr|sélectionn|montre)\w*[^.!?]*(figure|triangle|courbe|diagramme|schéma|graphique|tableau)/i;
const FIG_ASK = ['Entoure la figure pour que je la voie.', 'Entoure la figure dans le document : je pourrai la regarder avec toi.', 'Peux-tu entourer la figure ? Je la regarderai avec toi.'];

app.post('/api/chat', async (req, res) => {
  try {
    const { passages = [], history = [], l1 = 'fr', image = null } = req.body;
    const level = LEVELS[req.body.level] ? req.body.level : 'A2+', subject = subj(req.body.subject), mode = modeOf(req.body.mode);
    const correction = req.body.correction === true;                 // option enseignant : correction expliquée après plusieurs demandes d'aide
    const repere = String(req.body.repere || '').replace(/[«»\n]/g, ' ').trim().slice(0, 200);
    const doc = passages.map(label).join('\n'), docText = passages.map(p => p.t).join('\n');
    const hist = history.slice(-14).map(m => ({ role: m.role === 'assistant' ? 'assistant' : 'user', content: String(m.content || ''), lv: m.lv }));
    const lastLv = ([...hist].reverse().find(m => m.role === 'assistant' && LEVELS[m.lv]) || {}).lv;
    const changed = lastLv && lastLv !== level;
    const lastU = history.length ? String(history[history.length - 1].content || '') : '';
    const lu = lastLine(lastU).replace(/\(à propos de : [\s\S]*$/, '').trim();
    const isSel = /^\[SÉLECTION/.test(lastU), userLast = hist.length && hist[hist.length - 1].role === 'user';
    const pa = lastAssistant(history), laFr = typeof pa.fr === 'string' ? pa.fr : '';
    const prevAsked = /\?\s*$/.test(laFr.trim()), seed = history.length;
    const notes = [];
    const ctx = { laFr, noVerdict: false, leak: [], sel: '', allowOps: false, noBravo: false };
    let fallback = 'generic', relax = false, figureAsk = false, planKind = '';

    // 1. Ce que l'élève exprime : chaque situation devient une consigne, c'est le tuteur qui formule
    const intent = !image && !isSel && userLast ? intentOf(lu, laFr, mode) : null;
    if (intent && isHelpIntent(intent)) {
      const lvl = helpLevel(history, intent, { correction });
      notes.push(helpNote(lvl, intent, subject));
      fallback = intent === 'discour' ? 'discour' : 'help'; relax = lvl >= 3; ctx.allowOps = lvl >= 4; ctx.help = lvl;
    } else if (intent) {
      notes.push(situationNote(intent, lu)); fallback = intent;
      if (['echo', 'ack'].includes(intent)) ctx.noBravo = true;
      if (['ack', 'done'].includes(intent)) ctx.noQuestion = true;
    }

    const intentNotes = notes.length;   // consignes générales (aide, situations) : remplacées par celles de la fiche si elle existe
    // 1b. Maths, question d'exercice : le tuteur suit la fiche de la question, une étape à la fois (voir pedagogie.js)
    let track = sanitizeTrack(req.body.track), plan = null, planMode = false, turn = null, isNewQ = false, figNow = false, cq = null;
    if (subject === 'maths' && userLast && docText.length < 60000) {
      cq = currentQuestion({ lastU, isSel, image, repere, passages, track });
      if (cq) {
        isNewQ = !track || track.key !== cq.key;
        if (isNewQ) track = { key: cq.key, text: cq.text, label: cq.label, step: 0, tries: 0, helps: 0, fig: '', done: false };
        figNow = !!image && /Zone de «/.test(lastU);
      }
    }

    // 2. Maths, « Que veut dire fraction ? » : la définition relue du lexique (identique pour tous) ; si l'élève redemande, le tuteur réexplique autrement
    const lexA = subject === 'maths' && !image && userLast && !intent ? lexAnswer(lastU) : null;
    if (lexA) {
      const again = laFr && laFr.replace(/\s+/g, ' ').includes(lexA.fr.slice(0, 40));
      if (!again) {
        let l1t = '', motL1 = '';
        if (!NOL1(l1)) {
          try {
            const t = parseJson(await albert([{ role: 'system', content: `Tu traduis pour un élève allophone. Traduis fidèlement en ${LANGS[l1]}, sans rien ajouter. Réponds UNIQUEMENT par un objet JSON : {"l1": traduction du texte, "mot": traduction du mot}.` }, { role: 'user', content: JSON.stringify({ texte: lexA.fr, mot: lexA.word }) }]));
            l1t = typeof t.l1 === 'string' ? t.l1 : ''; motL1 = typeof t.mot === 'string' ? t.mot : '';
          } catch (e) { console.warn('traduction de la définition :', e.message); }
        }
        const pc = track && !track.done ? PLANS.get(planKey(track.text, track.fig, docText)) : null, back = pc && pc.etapes[track.step] ? ` Revenons à notre question : ${pc.etapes[track.step].question.charAt(0).toLowerCase() + pc.etapes[track.step].question.slice(1)}` : '';
        return res.json({ fr: lexA.fr + back, l1: back ? '' : l1t, cite: [], mots: lexA.word ? [{ fr: lexA.word, l1: motL1 }] : [], hors: true, track: track || undefined, niveau: { ...levelCheck(lexA.fr, level), corrige: false } });
      }
      notes.push(`[DÉFINITION DE RÉFÉRENCE (exacte) : « ${lexA.fr} ». L'élève redemande ce mot : ta première explication ne lui a pas suffi. Réexplique autrement, plus simplement, avec un AUTRE exemple de la vie courante, sans contredire cette définition. Commence par le mot avec son article.]`);
    }

    // 2b. La fiche de la question, et ce que l'élève fait par rapport à l'étape en cours
    if (cq) {
      plan = await getPlan(cq.text, docText, track.fig, figNow ? image : null);
      if (plan && figNow) track.fig = plan.figure_lue || 'figure entourée par l\'élève';   // même si le modèle ne la décrit pas : la figure est vue, on ne la redemande plus
      if (plan && (!track.done || (track.test && !isNewQ && !figNow) || isNewQ || figNow)) {
        if (track.done && (isNewQ || figNow)) track = { ...track, done: false, step: 0, tries: 0, helps: 0, stuck: 0, offer: false, shown: false, test: null };
        planMode = true;
        const asked = /entour\w*[^.!?]*(figure|diagramme|graphique|tableau|schéma|dessin|cercle)/i.test(laFr);
        let kind = figNow ? 'figure'
          : isSel || isNewQ ? (isNewQ ? 'new' : 'other')
            : intent === 'reformule' || intent === 'lost' || intent === 'rule' ? intent
            : intent && isHelpIntent(intent) ? 'help'
              : intent && ['ack', 'confirm', 'done', 'echo', 'hello'].includes(intent) ? 'ack'
                : ANSWERISH(lu) ? 'answer' : 'other';
        if (plan.figure && !track.fig && !figNow && !asked && ['new', 'other', 'ack'].includes(kind)) kind = 'figure-ask';
        const justifier = !(/aucune justification n['’]est (?:demandée|attendue)/i.test(docText) && /^question\s*\d+/i.test(track.label || ''));
        const next = mode === 'activite' ? nextQuestion(cq, passages) : null;
        // la règle utile : d'abord la définition courte du lexique (écrite pour A2+), puis la règle du cours ; d'abord ce que l'élève nomme, puis la notion de la fiche
        const lx = t => lexiconFor(t, 1).map(r => r.replace(/^- [^:]+ : /, ''));
        const rules = [...new Set([...lx(lu), ...toolsFor(lu, 1), ...toolsFor(plan.notion, 1), ...toolsFor(cq.text, 1), ...lx(plan.notion)].map(r => r.replace(/^- /, '')))].slice(0, 2);
        const args = { plan, track, kind, lu, intent, help: track.helps + 1, correction, mode, justifier, next, isNew: isNewQ, rules, level };
        turn = planTurn(args); planKind = kind;
        if (turn.chain && mode === 'activite' && next) {   // activité : on enchaîne sur la question suivante
          const np = await getPlan(next.text, docText, '', null);
          turn = planTurn({ ...args, nextPlan: np });
          if (np) turn.nextTrack = { key: next.key, text: next.text, label: next.label, step: 0, tries: 0, helps: 0, fig: '', done: false };
        }
        notes.splice(0, intentNotes); notes.push(turn.note);
        if (turn.lvl) { relax = turn.lvl >= 3; ctx.allowOps = turn.lvl >= 4; ctx.help = turn.lvl; }
        if (turn.reveal === 'tout' || kind === 'rule') relax = true;   // solution d'un test, petit test : un peu plus long
        // le contrat du message
        ctx.oneQuestion = !(turn.lvl >= 3); ctx.figSeen = !!(track.fig || figNow); ctx.noConfirm = kind === 'figure'; ctx.noTry = !turn.track.test;
        ctx.noApproval = turn.verdict === 'faux'; ctx.noBravo = false; ctx.noQuestion = false; ctx.allowRepeatQ = true; // reposer la question de l'étape est normal
        fallback = 'plan';
      }
    }

    // 3. Maths : lexique, méthodes, vrai calculateur, figures ; puis vérification d'un résultat annoncé (hors fiche)
    let mathVerdict = true, readV = null, solV = null, verifiedOk = false;
    if (subject === 'maths' && userLast) {
      const mn = mathsNotes(lastU, repere, !!image);
      figureAsk = mn.figureAsk && !intent && !planMode; mathVerdict = mn.verdict || planMode;
      notes.push(...(planMode ? mn.notes.filter(n => !/^\[(?:FIGURE|VÉRIFICATION)/.test(n)) : mn.notes));
      if (!planMode && !image && !mathVerdict && !isSel && !intent && docText.length < 60000) {
        const juste = (mode === 'ressource' ? "Puis arrête-toi, sans poser de nouvelle question sur le document." : "Puis passe à la question suivante de l'activité.") + (/aucune justification n['’]est (?:demandée|attendue)/i.test(docText) ? " Si cette question fait partie d'une partie où « aucune justification n'est demandée », ne parle pas de justification ; sinon, rappelle en une phrase qu'il faut écrire le calcul qui justifie." : " Rappelle en une phrase qu'au brevet on écrit aussi le calcul qui justifie.");
        const step = mode === 'ressource' ? "puis propose UNE petite étape suivante pour comprendre la question, sans donner la réponse." : "puis passe à la question suivante de l'exercice.";
        // a) réponse attendue de la question que le tuteur vient de poser (lue dans le document, preuve à l'appui)
        readV = readingVerdict(lu, pa, docText, false, step);
        const tutQ = askedNumber(laFr) ? laFr.trim() : '', focusQ = questionText(focusOf(lastU, repere), passages) || focusOf(lastU, repere), q = tutQ || focusQ;
        const given = pupilValue(lu);
        let kind = '';
        // b) sinon le modèle, pour lui seul, dit si la réponse se LIT (nombre + passage exact) ou se CALCULE (son calcul) ; l'outil contrôle l'un ou l'autre
        if (!readV && given !== null && q && !/^\s*\d+\s*$/.test(q)) {
          try {
            const g = tutQ ? await checkAnswer(q, 'Dernier message du tuteur', docText) : await cachedCheck(q, docText);
            kind = g && (g.type === 'lecture' || g.type === 'calcul') ? g.type : '';
            if (kind === 'lecture' && g.attendu !== null && g.attendu !== undefined) readV = readingVerdict(lu, { fr: q, attendu: String(g.attendu), preuve: String(g.preuve || '') }, docText, true, tutQ ? step : juste);
            if (kind === 'calcul') solV = solveVerdict(given, g, docText, tutQ ? step : juste);
          } catch (e) { console.warn('vérification :', e.message); }
        }
        const v = readV || solV;
        const lecture = kind ? kind === 'lecture' : isLecture(tutQ ? tutQ.split(/(?<=[.!?])\s+/).pop() : focusQ);
        if (v) { notes.push(v.note); mathVerdict = true; verifiedOk = v.ok; }
        else if (BARE_RESULT.test(lu) && prevAsked) { notes.push(`[L'élève répond à TA dernière question (« ${laFr.split(/(?<=[.!?])\s+/).pop()} »). Juge sa réponse par rapport à cette question, pas par rapport au document : si elle répond correctement, dis-le simplement et avance d'un pas vers la réponse de l'exercice ; sinon, dis ce qui peut être juste et aide-le avec un indice. Ne lui demande jamais où il lit ce nombre. Si ce que vous avez trouvé répond déjà à la question de l'exercice, dis-le clairement.]`); mathVerdict = true; fallback = 'generic'; }
        else if (BARE_RESULT.test(lu)) { notes.push(unknownNote(false)); fallback = 'unknown'; }
      }
      ctx.maths = true;
      if (!mathVerdict && !isSel && (/\d/.test(lu) || BARE_RESULT.test(lu))) ctx.noVerdict = true;   // pas de « c'est juste » sans l'outil (nombre ou lettre de QCM)
      ctx.sel = isSel ? ((lastU.match(/«\s*([\s\S]*?)\s*»/) || [])[1] || '') : '';
      ctx.leak = ctx.help >= 5 ? [] : [...leakValues(ctx.sel || repere), ...(readV && !readV.ok ? [readV.value] : []), ...(solV && !solV.ok ? solV.forms : [])];
      // La réponse de la question en cours, sous toutes ses écritures (3/4, 75/100, « trois quarts »…) : jamais soufflée, sauf correction autorisée ou réponse juste de l'élève
      if (planMode) {
        const avoid = cq.text + ' ' + history.filter(m => m.role === 'user').map(m => lastLine(m.content)).join(' ');
        const lk = planLeaks(plan, turn.track, avoid);
        ctx.leak = [...ctx.leak.filter(x => !avoid.replace(/\s/g, '').includes(x)), ...lk.nums]; ctx.leakWords = lk.words; ctx.qcm = plan.lettre && !turn.track.done ? (qcmOption(cq.text, plan.final) || { letter: plan.lettre, text: '\u0000' }) : null;
        if (ctx.help >= 5 || turn.reveal === 'tout') { ctx.leak = []; ctx.leakWords = []; ctx.qcm = null; }
      } else if (!image && !(ctx.help >= 4) && !verifiedOk && docText.length < 60000) { // à l'étape 4 (première étape faite ensemble), une écriture intermédiaire peut être donnée
        const qx = questionText(isSel ? ctx.sel : focusOf(lastU, repere), passages);
        if (qx.length >= 12 && isQuestion(qx)) {
          const v = calcValue(await cachedCheck(qx, docText));
          if (v !== null) { const f = answerForms(v, qx + ' ' + lastU); ctx.leak.push(...f.nums); ctx.leakWords = f.words; ctx.qcm = qcmOption(qx, v); }
        }
      }
    }
    if (mode === 'ressource' && !prevAsked && !intent && (isSel || /\?\s*$/.test(lu)) && !verifiedOk) ctx.noBravo = true; // l'élève demande quelque chose : pas de « bravo », il n'a encore rien répondu (« je comprends maintenant ! » peut être félicité)

    // 4. Message envoyé au modèle
    if (userLast) {
      if (repere && !isSel) notes.push(`[REPÈRE : l'élève vient de travailler « ${repere} ». Si tu proposes la suite ou une question, pars de cet endroit du document (jamais du début) et ne reviens pas sur ce qui vient d'être expliqué.]`);
      if (changed) notes.push(`[CHANGEMENT DE NIVEAU : le niveau vient de passer de ${lastLv} à ${level}. N'imite pas le style de tes messages précédents : écris comme dans la description du niveau ${level}. Ne le dis pas à l'élève.]`);
      if (notes.length) hist[hist.length - 1].content += '\n' + notes.filter(Boolean).join('\n');
    }
    const msgs = [{ role: 'system', content: system(l1, level, subject, mode) + scopeLine(req.body.section) + `\n\n${mode === 'activite' ? "Activité de l'élève" : 'Document à lire'} :\n${doc}` }, ...hist.map(({ role, content }) => ({ role, content }))];
    let model = ALBERT_MODEL;
    if (image) { // zone entourée par l'élève : envoyée au modèle qui lit les images
      if (typeof image !== 'string' || !image.startsWith('data:image/') || image.length > 4000000) return res.status(400).json({ error: 'Image invalide.' });
      if (!ALBERT_VISION_MODEL) return res.status(400).json({ error: "Aucun modèle d'image configuré (ALBERT_VISION_MODEL)." });
      model = ALBERT_VISION_MODEL;
      const last = msgs[msgs.length - 1];
      msgs[msgs.length - 1] = { role: 'user', content: [{ type: 'text', text: last.content }, { type: 'image_url', image_url: { url: image } }] };
    }
    let out = parseJson(await albert(msgs, { model }));
    out = await short(out, msgs, model, level, relax ? 1 : 0);        // un exemple résolu, un rappel de règle, une correction : plus longs, mais toujours au niveau
    const corr = !!out.corrige;
    if (!image && !intent && !planMode) out = await grounded(out, msgs, model, level, passages);
    if (!planMode) out = await onSelection(out, msgs, model, level, image);
    const finish = o => {
      o = tidyReply(o, mode, lu, seed, !!(planMode && turn && turn.track.offer));
      let fr = mathSigns(o.fr);
      if (subject === 'maths') fr = sansRaccourci(fr, docText);
      return fr === o.fr ? o : { ...o, fr };
    };
    out = finish(out);

    // 5. Contrôles : si la réponse enfreint une règle, le tuteur la réécrit lui-même (une fois) ; sinon on retire le passage fautif ; une phrase de secours en tout dernier recours
    let iss = issuesOf(out.fr, ctx);
    if (iss.length) {
      try {
        let again = parseJson(await albert([...msgs, { role: 'assistant', content: JSON.stringify(out) }, { role: 'user', content: `Réécris ta réponse pour l'élève. À corriger : ${iss.map(i => i.msg).join(' ; ')}. Garde un ton chaleureux et naturel, des phrases courtes (niveau ${level}). Ne réponds pas à cette consigne et n'écris aucune formule comme « d'accord » ou « c'est compris » : écris directement ta nouvelle réponse. Même format JSON.` }], { model }));
        if (!derailed(out, again, false)) {
          again = finish(again);
          const iss2 = issuesOf(again.fr, ctx);
          if (iss2.length < iss.length) { if (!again.cite && out.cite) again.cite = out.cite; out = again; iss = iss2; }
        }
      } catch (e) { console.warn('réécriture :', e.message); }
      if (iss.length) {
        const fixed = repair(out.fr, ctx);
        const planQ = planMode && plan.etapes[Math.min(turn.track.step, plan.etapes.length - 1)] ? plan.etapes[Math.min(turn.track.step, plan.etapes.length - 1)].question : '';
        out = { ...out, fr: fixed && words(fixed) >= 3 ? fixed : (planQ && !turn.track.done ? planQ : pick(fallback, seed, laFr)), l1: '' }; // traduction refaite à la demande
      }
    }
    // 6. Figure invisible : une invitation, une seule, avec le bon verbe (une figure s'entoure)
    if (figureAsk && typeof out.fr === 'string') {
      const ss = out.fr.split(/(?<=[.!?])\s+/).filter(Boolean);
      const k = ss.findIndex(x => FIG_INVITE.test(x));
      let fr;
      if (k >= 0) { ss[k] = ss[k].replace(/\b(?:surligne|encadre|sélectionne|montre)(?:-moi)?\b/i, 'Entoure'); fr = ss.filter((x, i) => i === k || !FIG_INVITE.test(x)).join(' '); }
      else fr = `${out.fr.trim()} ${FIG_ASK[seed % FIG_ASK.length]}`;
      if (fr !== out.fr) out = { ...out, fr, l1: '' };
    }
    // 7b. Repères garantis (le modèle les oublie parfois) : le point quand l'élève est perdu, l'annonce de la question suivante
    if (planMode && typeof out.fr === 'string') {
      const ss = out.fr.split(/(?<=[.!?])\s+/).filter(Boolean);
      if (planKind === 'lost' && !/cherch/i.test(out.fr)) {
        const k = Math.min(turn.track.step, plan.etapes.length);
        const quoi = String(plan.cherche || '').replace(/^\s*(?:on cherche|chercher|trouver)\s*(?::\s*)?/i, '').replace(/[.\s]+$/, '');
        const fait = k > 0 ? ` Ce qu'on a déjà trouvé : ${plan.etapes.slice(0, k).map(e => e.attendu.replace(/[.\s]+$/, '')).join(' ; ')}.` : ' On commence par une petite étape.';
        const point = quoi ? `On fait le point. Ce qu'on cherche : ${quoi.charAt(0).toLowerCase() + quoi.slice(1)}.${fait}` : '';
        if (point) { ss.splice(ss.length > 1 ? 1 : 0, 0, point); out = { ...out, fr: ss.join(' '), l1: '' }; }
      }
      const nt = turn.nextTrack;
      if (nt && nt.label && !new RegExp(nt.label.replace(/\s+/g, '\\s*'), 'i').test(out.fr)) {
        const ss2 = out.fr.split(/(?<=[.!?])\s+/).filter(Boolean), qi = ss2.map(x => /\?\s*$/.test(x)).lastIndexOf(true);
        ss2.splice(qi >= 0 ? qi : ss2.length, 0, `Passons à la ${nt.label.charAt(0).toLowerCase() + nt.label.slice(1)}.`);
        out = { ...out, fr: ss2.join(' '), l1: '' };
      }
    }
    // 8. Le suivi de la question : mis à jour et renvoyé à l'interface (qui le renverra au prochain message)
    if (planMode) {
      let t = turn.track;
      if (turn.verdict === 'modele') {              // réponse en mots : c'est le tuteur qui a jugé (champ "etape")
        const ok = /^juste/i.test(String(out.etape || ''));
        if (ok) { t = { ...t, step: t.step + 1, tries: 0, helps: 0, stuck: 0 }; if (t.step >= plan.etapes.length) t = { ...t, done: true }; out.juste = true; }
        else t = { ...t, tries: t.tries + 1 };
      }
      if (turn.verdict === 'juste') out.juste = true;
      if (t.test && t.test.pending) {              // petit test proposé : sa réponse, calculée par l'outil (jamais celle du modèle)
        const ss = String(out.fr || '').split(/(?<=[.!?])\s+/), q = ss.filter(x => /\?\s*$/.test(x)).pop() || '';
        const v = typeof out.test_calcul === 'string' && out.test_calcul.trim() ? calcValue({ calcul: out.test_calcul, resultat: '' }) : null;
        t = { ...t, test: q ? { pending: false, v, q: q.slice(0, 240) } : null };
      }
      out.track = turn.nextTrack || t;
    } else if (track) out.track = track;
    delete out.etape; delete out.test_calcul;
    if (verifiedOk || notes.some(n => /(?:Verdict : |» : )JUSTE/.test(n))) out.juste = true; // pour le bilan de l'effort de l'élève
    if (ctx.help) out.aide = ctx.help;
    // 7. Comprendre : une question de l'exercice vient d'être expliquée ; la suite logique, c'est d'essayer (pas « surligne autre chose ») — hors fiche
    if (!planMode && mode === 'ressource' && isSel && !image && !figureAsk && !intent && typeof out.fr === 'string' && !/\?\s*$/.test(out.fr.trim())) {
      const selq = questionText((lastU.match(/«\s*([\s\S]*?)\s*»/) || [])[1] || '', passages);
      if (selq.length >= 12 && isQuestion(selq)) {
        const ss = out.fr.split(/(?<=[.!?])\s+/).filter(Boolean);
        while (ss.length > 1 && INVITE_RE.test(ss[ss.length - 1].trim())) ss.pop();
        if (!/écris ta réponse|à toi/i.test(ss.join(' '))) out = { ...out, fr: `${ss.join(' ')} ${TRY[seed % TRY.length]}`, l1: '' };
      }
    }
    delete out.corrige; out.niveau = { ...levelCheck(out.fr, level, relax ? 1 : 0), corrige: corr };
    res.json(out);
  } catch (e) { console.error(e); res.status(500).json({ error: e.message }); }
});

// ---------- Point rapide : question posée par le tuteur ----------
const CHECK_TYPES = ['inference', 'qcm', 'reformuler', 'confiance'];
const normTxt = x => String(x || '').normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase().replace(/[^a-z0-9]/g, '');
const tokens = x => String(x || '').normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase().match(/[a-z0-9]{3,}/g) || [];
// Retrouve le passage qui contient la citation donnée par le modèle (null si introuvable)
function findQuote(passages, q) {
  const nq = normTxt(q);
  if (nq.length < 8) return null;
  for (const p of passages) if (normTxt(p.t).includes(nq)) return p.id;
  const qt = tokens(q); let best = null, score = 0;
  for (const p of passages) {
    const pt = new Set(tokens(p.t)), sc = qt.filter(t => pt.has(t)).length / (qt.length || 1);
    if (sc > score) { score = sc; best = p.id; }
  }
  return score >= 0.7 ? best : null;
}
const STOP = new Set('les des une dans pour avec sont est que qui quoi par sur pas plus mais donc comme elle ils elles nous vous son ses leur leurs cette ces aux the'.split(' '));
const content = x => tokens(x).filter(t => !STOP.has(t));
// La bonne réponse ne doit pas être une simple copie de ce que le tuteur vient d'expliquer
function recall(opt, botFr) {
  const o = content(opt); if (!o.length) return false;
  const b = new Set(content(botFr));
  return o.filter(t => b.has(t)).length / o.length >= 0.8;
}
// Radicaux (6 lettres) des mots que l'élève vient de faire expliquer : ils ne doivent pas figurer dans la question
function stems(lastUser) {
  const m = String(lastUser).match(/[«“"]([^»”"]{1,60})[»”"]/);
  const base = m && words(m[1]) <= 3 ? m[1] : '';
  return content(base).filter(t => t.length >= 5).map(t => t.slice(0, 6));
}
const touches = (text, st) => { const t = tokens(text); return st.some(s => t.some(w => w.startsWith(s))); };

function normalizeCheckin(r, passages = []) {
  if (!r || !CHECK_TYPES.includes(r.type) || typeof r.fr !== 'string' || !r.fr.trim())
    return { type: 'confiance', fr: 'Tu peux expliquer avec tes mots ce que tu viens de lire ?', l1: '' };
  const out = { type: r.type, fr: clean(r.fr.trim()), l1: typeof r.l1 === 'string' ? clean(r.l1) : '' };
  if (r.type === 'qcm' || r.type === 'inference') {
    const raw = Array.isArray(r.options) ? r.options.slice(0, 3) : [];
    const valid = raw.length >= 2 && raw.every(x => x && typeof x.fr === 'string' && x.fr.trim())
      && Number.isInteger(r.bonne) && r.bonne >= 0 && r.bonne < raw.length;
    const pid = r.indice ? findQuote(passages, r.indice) : null;
    // une question d'inférence doit s'appuyer sur un indice réellement présent dans le texte
    if (!valid || (r.type === 'inference' && !pid)) { out.type = 'reformuler'; out.downgraded = true; return out; }
    const opts = raw.map((x, i) => ({ fr: x.fr.trim(), l1: typeof x.l1 === 'string' ? x.l1 : '', good: i === r.bonne }));
    for (let i = opts.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [opts[i], opts[j]] = [opts[j], opts[i]]; }
    out.options = opts.map(({ fr, l1 }) => ({ fr, l1 }));
    out.bonne = opts.findIndex(x => x.good);
    const e = r.explication || {};
    out.explication = { fr: typeof e.fr === 'string' ? e.fr : '', l1: typeof e.l1 === 'string' ? e.l1 : '' };
    if (pid) { out.indice = String(r.indice).trim(); out.pid = pid; }
  }
  return out;
}
// Raisons pour lesquelles on refuse une question de point rapide
function checkinProblems(res, ctx) {
  const out = [], L = lv(ctx.level);
  if (res.type === 'qcm' || res.type === 'inference') {
    const good = res.options[res.bonne];
    if (recall(good.fr, ctx.botFr)) out.push("la bonne réponse recopie l'explication que le tuteur vient de donner : ce serait du rappel, pas une déduction");
    if (res.type === 'inference') {
      if (touches(res.fr, ctx.stems) || touches(res.indice, ctx.stems)) out.push("la question ou l'indice contient le mot que l'élève vient de faire expliquer : choisis un AUTRE indice du texte");
      if (res.options.some(o => touches(o.fr, ctx.stems))) out.push("une option reprend le mot qui vient d'être expliqué");
    }
    if (res.options.some(o => words(o.fr) > L.optWords + 2)) out.push(`options trop longues (${L.optWords} mots maximum)`);
  }
  out.push(...levelIssues(res.fr, ctx.level));
  return out;
}
function fallbackCheckin(level) {
  return { type: 'reformuler', fr: level === 'B1' ? 'Redis avec tes mots, en deux phrases, ce que tu viens de lire.' : 'Redis avec tes mots ce que tu viens de lire.', l1: '' };
}
async function buildCheckin(sys, hist, ctx, passages) {
  const base = [{ role: 'system', content: sys }, ...hist.slice(-6), { role: 'user', content: '[POINT À PRÉPARER] Prépare la question de point rapide.' }];
  const ok = r => !r.downgraded && !checkinProblems(r, ctx).length;
  let res = normalizeCheckin(parseJson(await albert(base)), passages);
  if (ok(res)) return finish(res, ctx);
  const why = res.downgraded ? "il manque un indice EXACT du texte ou des options valides" : checkinProblems(res, ctx).join(' ; ');
  const again = [...base, { role: 'assistant', content: JSON.stringify(res) }, { role: 'user', content: `Refusé : ${why}. Propose une autre question, même format JSON.` }];
  res = normalizeCheckin(parseJson(await albert(again)), passages);
  return ok(res) ? finish(res, ctx) : fallbackCheckin(ctx.level);
}
function finish(res, ctx) {
  if (res.type === 'reformuler') res.fr = fallbackCheckin(ctx.level).fr; // formulation sûre, adaptée au niveau
  delete res.downgraded;
  return res;
}
// Traduction à la demande : fonctionne sur n'importe quel message, même si le tuteur n'en a pas fourni
app.post('/api/translate', async (req, res) => {
  try {
    const l1 = req.body.l1;
    if (!LANGS[l1] || NOL1(l1)) return res.status(400).json({ error: 'Choisis d\'abord ta langue.' });
    const texts = (Array.isArray(req.body.texts) ? req.body.texts : []).slice(0, 8).map(t => String(t || '').slice(0, 700));
    if (!texts.length || texts.every(t => !t.trim())) return res.status(400).json({ error: 'Rien à traduire.' });
    const sys = `Tu traduis du français scolaire vers cette langue : ${LANGS[l1]}, pour un élève allophone. Traduction fidèle, simple, de même longueur : rien en plus, rien en moins, aucune explication. Les mots français entre « » restent entre « » (ajoute leur équivalent à côté si utile). Réponds UNIQUEMENT par un objet JSON : {"t": [une traduction par texte, dans le même ordre, chaîne vide si le texte est vide]}.`;
    const out = parseJson(await albert([{ role: 'system', content: sys }, { role: 'user', content: JSON.stringify({ textes: texts }) }]));
    let t = Array.isArray(out.t) ? out.t : [];
    t = texts.map((_, i) => (typeof t[i] === 'string' ? t[i].trim() : ''));
    if (!t.some(Boolean)) throw new Error('Traduction indisponible. Réessaie.');
    res.json({ t });
  } catch (e) { console.error(e); res.status(500).json({ error: e.message }); }
});

app.post('/api/checkin', async (req, res) => {
  try {
    const { passages = [], history = [], l1 = 'fr' } = req.body;
    const level = LEVELS[req.body.level] ? req.body.level : 'A2+', subject = subj(req.body.subject), L = lv(level);
    if (!LANGS[l1]) return res.status(400).json({ error: 'Langue inconnue.' });
    // Ce que l'élève vient de travailler : dernière demande, dernière explication, passage montré
    const rev = [...history].reverse();
    const lastUser = (rev.find(m => m.role === 'user') || {}).content || '';
    let botFr = '', cited = '';
    try {
      const j = JSON.parse((rev.find(m => m.role === 'assistant') || {}).content || '{}');
      botFr = j.fr || '';
      cited = (j.cite || j.refs || []).map(id => (passages.find(p => p.id === +id) || {}).t).filter(Boolean).join(' ');
    } catch {}
    const focus = `- Dernière demande de l'élève : « ${String(lastUser).slice(0, 300)} »\n- Dernière explication du tuteur : « ${botFr.slice(0, 300)} »\n- Passage concerné : « ${cited.slice(0, 400) || 'voir la demande ci-dessus'} »`;
    const S = SUBJECTS[subject];
    const sys = `Tu prépares UNE question de « point rapide » pour un élève allophone (niveau ${level} du CECRL en français scolaire, langue première : ${LANGS[l1]}). Matière : ${S.nom}.
Elle doit porter sur CE QUE L'ÉLÈVE VIENT DE TRAVAILLER (voir plus bas), jamais sur un autre endroit du texte. N'invente rien : appuie-toi uniquement sur le texte de l'activité. Ne demande JAMAIS « tu comprends ? ».
Deux niveaux de questions : littérale (la réponse est écrite dans le texte) ou INFÉRENCE (la réponse n'est PAS écrite mais se déduit d'indices du texte). Privilégie l'inférence dès que le passage s'y prête. ${S.infer}
Types :
- "inference" : question de déduction. Elle doit relier AU MOINS UN indice du texte à une conclusion que le texte NE DIT PAS (sentiment, saison, cause, statut, conséquence…). Type de déduction attendu : ${S.hint}.
  * L'indice ("indice" = citation EXACTE du texte, 10 mots maximum) ne doit PAS contenir le mot que le tuteur vient d'expliquer, et la question non plus : sinon l'élève répond par simple rappel.
  * La bonne réponse ne doit JAMAIS être recopiée de l'explication du tuteur.
  * 3 options : UNE seule juste d'après le texte ; les deux autres sont CONTREDITES par le texte (aucune ambiguïté).
  * "explication" : « Le texte dit …, donc … » (1 phrase).
- "qcm" : question littérale sur une autre information du même passage (3 options, UNE seule juste, les autres contredites par le texte). "indice" facultatif.
- "reformuler" : demande de redire avec ses mots l'idée qui vient d'être travaillée.
- "confiance" : seulement si l'élève semble en difficulté ou n'a presque rien dit.
Niveau ${level} : question de ${L.maxWords} mots maximum, ${L.profil.split('\n')[0].replace(/^- /, '').toLowerCase()} Options de ${L.optWords} mots maximum. Ne donne jamais la réponse de l'exercice.
Réponds UNIQUEMENT par un objet JSON : {"type": "inference" | "qcm" | "reformuler" | "confiance", "fr": string, "l1": string (${trad(l1)}), "options": [{"fr": string, "l1": string}] (inference et qcm), "bonne": numéro de la bonne option, de 0 à 2, "indice": string, "explication": {"fr": string, "l1": string}}

CE QUE L'ÉLÈVE VIENT DE TRAVAILLER :
${focus}

Texte de l'activité :
${passages.map(label).join('\n')}`;
    res.json(await buildCheckin(sys, history, { level, botFr, stems: stems(lastUser) }, passages));
  } catch (e) { console.error(e); res.status(500).json({ error: e.message }); }
});


// ---------- Quiz de fin d'activité : 5 questions (A2+) ou 8 (B1), littérales / inférentielles / vocabulaire ----------
const QUIZ_PLAN = { 'A2+': { litteral: 2, inference: 2, vocabulaire: 1 }, 'B1': { litteral: 3, inference: 3, vocabulaire: 2 } };
const QUIZ_KINDS = ['litteral', 'inference', 'vocabulaire'];
function quizProblems(q, level, passages) {
  const L = lv(level), out = [];
  const wc = t => String(t || '').trim().split(/\s+/).filter(Boolean).length;
  if (wc(q.fr) > L.maxWords + 4) out.push('question trop longue');
  if (L.banned && (L.banned.test(q.fr) || q.options.some(o => L.banned.test(o.fr)))) out.push('mot ou tournure hors niveau');
  if (q.options.some(o => wc(o.fr) > L.optWords + 2)) out.push('option trop longue');
  if (new Set(q.options.map(o => normTxt(o.fr))).size < q.options.length) out.push('options identiques');
  if (q.kind === 'inference') {
    const good = q.options[q.bonne].fr, p = passages.find(x => x.id === q.pid);
    if (p && normTxt(p.t).includes(normTxt(good)) && normTxt(good).length > 6) out.push('inférence : la bonne réponse est écrite telle quelle dans le texte');
  }
  return out;
}
function normalizeQuizItem(r, passages) {
  if (!r || !QUIZ_KINDS.includes(r.kind) || typeof r.fr !== 'string' || !r.fr.trim()) return null;
  const raw = Array.isArray(r.options) ? r.options.slice(0, 3) : [];
  if (raw.length !== 3 || !raw.every(x => x && typeof x.fr === 'string' && x.fr.trim())) return null;
  if (!Number.isInteger(r.bonne) || r.bonne < 0 || r.bonne > 2) return null;
  const pid = r.indice ? findQuote(passages, r.indice) : null;
  if (!pid) return null; // chaque question s'appuie sur une citation exacte du document
  const opts = raw.map((x, i) => ({ fr: clean(x.fr.trim()), l1: typeof x.l1 === 'string' ? clean(x.l1) : '', good: i === r.bonne }));
  for (let i = opts.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [opts[i], opts[j]] = [opts[j], opts[i]]; }
  const e = r.explication || {};
  return {
    kind: r.kind, fr: clean(r.fr.trim()), l1: typeof r.l1 === 'string' ? clean(r.l1) : '',
    options: opts.map(({ fr, l1 }) => ({ fr, l1 })), bonne: opts.findIndex(x => x.good),
    indice: String(r.indice).trim().slice(0, 200), pid,
    explication: { fr: typeof e.fr === 'string' ? clean(e.fr) : '', l1: typeof e.l1 === 'string' ? clean(e.l1) : '' }
  };
}
app.post('/api/quiz', async (req, res) => {
  try {
    const { passages = [], l1 = 'fr' } = req.body;
    if (!LANGS[l1]) return res.status(400).json({ error: 'Langue inconnue.' });
    const level = LEVELS[req.body.level] ? req.body.level : 'A2+', subject = subj(req.body.subject), mode = modeOf(req.body.mode), L = lv(level), S = SUBJECTS[subject];
    const ps = passages.slice(0, 120).map(p => ({ id: +p.id, t: String(p.t || '').slice(0, 600), type: p.type }));
    if (!ps.length) return res.status(400).json({ error: 'Aucun document.' });
    const plan = QUIZ_PLAN[level], total = plan.litteral + plan.inference + plan.vocabulaire;
    const asked = (Array.isArray(req.body.deja) ? req.body.deja : []).slice(0, 20).map(x => String(x).slice(0, 120));
    const sys = `Tu prépares un petit quiz de compréhension pour un élève allophone (niveau ${level} du CECRL, français scolaire ; langue première : ${LANGS[l1]}). Matière : ${S.nom}. ${mode === 'activite' ? "Le document est une activité scolaire : ne pose JAMAIS les questions de l'exercice et ne donne jamais leur réponse ; teste seulement la compréhension du contenu (documents, énoncé, consigne)." : 'Le document est une ressource à comprendre.'}
Fais EXACTEMENT ${total} questions : ${plan.litteral} "litteral", ${plan.inference} "inference", ${plan.vocabulaire} "vocabulaire".
- litteral : la réponse est écrite dans le texte.
- inference : la réponse n'est PAS écrite telle quelle mais se déduit d'un indice du texte. ${S.infer} Déduction attendue : ${S.hint}.
- vocabulaire : sens d'un mot ou d'une expression DANS CE TEXTE (pas le sens général du dictionnaire).
Règles pour CHAQUE question : 3 options (une seule juste d'après le texte ; les deux autres CONTREDITES par le texte, aucune ambiguïté) ; "bonne" = numéro 0, 1 ou 2 de la bonne option ; "indice" = citation EXACTE du texte (10 mots maximum) qui justifie la bonne réponse ; "explication" = 1 phrase simple « Le texte dit …, donc … » ; "l1" = ${trad(l1)} (aussi pour chaque option et pour l'explication).
Niveau ${level} : question de ${L.maxWords} mots maximum ; options de ${L.optWords} mots maximum ; ${L.profil.split('\n')[0].replace(/^- /, '').toLowerCase()} N'invente rien qui ne soit pas dans le texte. Varie les passages. Ordre des questions : de la plus simple à la plus difficile.${asked.length ? `\nQuestions déjà posées (ne les répète pas) : ${asked.join(' | ')}` : ''}
Réponds UNIQUEMENT par un objet JSON : {"questions":[{"kind":"litteral"|"inference"|"vocabulaire","fr":string,"l1":string,"options":[{"fr":string,"l1":string},{"fr":string,"l1":string},{"fr":string,"l1":string}],"bonne":number,"indice":string,"explication":{"fr":string,"l1":string}}]}

${subject === 'maths' ? `\nMATHÉMATIQUES : aucune question de calcul, aucun résultat à trouver. litteral = quelle donnée l'énoncé donne, ou ce que demande la question ; inference = quelle opération, propriété ou formule choisir (sans l'appliquer) ; vocabulaire = un mot ou une consigne mathématique, avec ces définitions fiables :\n${lexiconAll(ps.map(p => p.t).join(' ')).join('\n') || '(aucune)'}\n` : ''}\nTexte :\n${ps.map(label).join('\n')}`;
    const base = [{ role: 'system', content: sys }, { role: 'user', content: 'Prépare le quiz.' }];
    const take = (raw, have) => {
      for (const r of Array.isArray(raw && raw.questions) ? raw.questions : []) {
        const q = normalizeQuizItem(r, ps);
        if (!q || quizProblems(q, level, ps).length) continue;
        if (have.some(h => normTxt(h.fr) === normTxt(q.fr))) continue;
        have.push(q);
      }
      return have;
    };
    let items = take(parseJson(await albert(base)), []);
    const count = k => items.filter(x => x.kind === k).length;
    const missing = QUIZ_KINDS.filter(k => count(k) < plan[k]);
    if (missing.length) { // une seule relance, pour les types manquants
      const need = missing.map(k => `${plan[k] - count(k)} "${k}"`).join(', ');
      const again = [...base, { role: 'assistant', content: JSON.stringify({ questions: items }) }, { role: 'user', content: `Il manque : ${need}. Propose seulement ces questions, même format JSON, avec des citations exactes et un niveau ${level}.` }];
      items = take(parseJson(await albert(again)), items);
    }
    const ordered = [];
    for (const k of QUIZ_KINDS) ordered.push(...items.filter(x => x.kind === k).slice(0, plan[k]));
    // ordre : littérales, puis inférences, puis vocabulaire entrelacé pour varier
    const out = [], pools = QUIZ_KINDS.map(k => ordered.filter(x => x.kind === k));
    while (pools.some(p => p.length)) for (const p of pools) if (p.length) out.push(p.shift());
    if (out.length < Math.min(3, total)) return res.status(502).json({ error: "Le tuteur n'a pas pu préparer le quiz. Réessaie dans un instant." });
    res.json({ total: out.length, questions: out });
  } catch (e) { console.error(e); res.status(500).json({ error: e.message }); }
});

// ---------- Bilan enseignant : analyse du travail de l'élève (rien n'est enregistré sur le serveur) ----------
const EV_TYPES = new Set(['aide', 'mot', 'traduction', 'question', 'reponse', 'bouton', 'indice', 'indice_propose', 'point_pose', 'point_qcm', 'point_confiance', 'reformulation', 'point_plus_tard', 'section', 'travail', 'quiz', 'quiz_fin']);
const EV_KEYS = ['texte', 'fr', 'l1', 'avec_langue', 'image', 'q', 'kind', 'reponse', 'juste', 'niveau', 'statut', 'label', 'lie'];
function sanitizeEvents(evs) {
  if (!Array.isArray(evs)) return [];
  return evs.slice(0, 300).filter(e => e && EV_TYPES.has(e.type)).map(e => {
    const o = { type: e.type, t: Math.max(0, Math.round(+e.t || 0)) };
    for (const k of EV_KEYS) if (e[k] !== undefined && e[k] !== null) o[k] = typeof e[k] === 'string' ? e[k].slice(0, k === 'texte' && e.type === 'travail' ? 700 : 300) : (typeof e[k] === 'boolean' || typeof e[k] === 'number' ? e[k] : undefined);
    return o;
  });
}
function computeStats(evs, duree) {
  const c = t => evs.filter(e => e.type === t);
  const qcm = c('point_qcm'), inf = qcm.filter(e => e.kind === 'inference'), lit = qcm.filter(e => e.kind !== 'inference');
  return {
    duree_min: Math.max(1, Math.round((+duree || (evs.length ? evs[evs.length - 1].t : 0)) / 60)),
    aides: c('aide').length, aides_avec_langue: c('aide').filter(e => e.avec_langue).length + c('traduction').length,
    questions_libres: c('question').length, reponses: c('reponse').length,
    reponses_activite: c('reponse').filter(e => e.kind === 'activite').length, comprehension_ecrite: c('reponse').filter(e => e.kind === 'comprehension').length, mots_cliques: c('mot').length,
    mots_surlignes: c('aide').filter(e => e.texte && words(e.texte) <= 2).length,
    qcm: { total: lit.length, justes: lit.filter(e => e.juste).length },
    inference: { total: inf.length, justes: inf.filter(e => e.juste).length, indice_trouve: c('indice').filter(e => e.statut === 'trouve').length, indice_montre: c('indice').filter(e => e.statut === 'montre').length, indice_rate: c('indice').filter(e => e.statut === 'rate').length },
    quiz: (() => { const q = c('quiz'), by = k => { const a = q.filter(e => e.kind === k); return { total: a.length, justes: a.filter(e => e.juste).length }; }; return { total: q.length, justes: q.filter(e => e.juste).length, litteral: by('litteral'), inference: by('inference'), vocabulaire: by('vocabulaire') }; })(),
    confiance: c('point_confiance').map(e => e.niveau).filter(Boolean),
    reformulations: c('reformulation').length, points_reportes: c('point_plus_tard').length,
    boutons: c('bouton').length, parties_vues: c('section').length, travaux: c('travail').length
  };
}
const arr = (x, n = 6, m = 300) => (Array.isArray(x) ? x : []).filter(s => typeof s === 'string' && s.trim()).slice(0, n).map(s => s.slice(0, m));
const str = (x, m = 600) => (typeof x === 'string' ? x.slice(0, m) : '');
function normalizeReport(r) {
  r = r && typeof r === 'object' ? r : {};
  const v = r.vocabulaire || {}, c = r.comprehension || {}, p = r.production || {}, n = r.niveau_indicatif || {};
  return {
    resume: str(r.resume), points_forts: arr(r.points_forts), difficultes: arr(r.difficultes),
    vocabulaire: { acquis: arr(v.acquis, 10, 80), a_retravailler: arr(v.a_retravailler, 10, 80) },
    comprehension: { litterale: str(c.litterale, 300), inference: str(c.inference, 300) },
    production: {
      observations: str(p.observations, 500), erreurs_recurrentes: arr(p.erreurs_recurrentes, 5),
      traductions: (Array.isArray(p.traductions) ? p.traductions : []).filter(t => t && typeof t.texte === 'string').slice(0, 5).map(t => ({ texte: str(t.texte, 300), fr: str(t.fr, 300) }))
    },
    travail: str(r.travail, 600), besoins_tutorat: str(r.besoins_tutorat, 500), autonomie: str(r.autonomie, 400),
    niveau_indicatif: { reception: str(n.reception, 20), production: str(n.production, 20), reserve: str(n.reserve, 300) },
    recommandations: arr(r.recommandations, 3, 300)
  };
}
app.post('/api/report', async (req, res) => {
  try {
    const { passages = [], l1 = 'fr', titre = '', duree = 0 } = req.body;
    const level = LEVELS[req.body.level] ? req.body.level : 'A2+', subject = subj(req.body.subject), mode = modeOf(req.body.mode);
    if (!LANGS[l1]) return res.status(400).json({ error: 'Langue inconnue.' });
    const events = sanitizeEvents(req.body.events), stats = computeStats(events, duree);
    if (events.length < 2) return res.json({ stats, analyse: null, partiel: true });
    const S = SUBJECTS[subject];
    const trace = events.map(e => `${String(Math.floor(e.t / 60)).padStart(2, '0')}:${String(e.t % 60).padStart(2, '0')} ${e.type} ${JSON.stringify(Object.fromEntries(Object.entries(e).filter(([k]) => k !== 'type' && k !== 't')))}`).join('\n');
    const sys = `Tu aides un enseignant à suivre un élève allophone (langue première : ${LANGS[l1]}, niveau visé ${level} du CECRL, matière : ${S.nom}) qui a travaillé avec un tuteur numérique. À partir des traces ci-dessous, rédige un bilan FACTUEL, NON JUGEANT, utile pour la suite de l'accompagnement.
Le document est : ${mode === 'activite' ? 'une ACTIVITÉ scolaire avec consigne' : 'une RESSOURCE à lire, sans consigne (il n\'y a donc pas d\'activité scolaire à évaluer)'}. Distingue deux choses dans les traces : (1) le TRAVAIL de l'élève = ses événements « reponse » (ses réponses aux questions du tuteur), « travail » (texte écrit dans son espace « Mon travail » et soumis à la relecture : analyse sa langue, ses erreurs récurrentes et ses progrès d'une version à l'autre), « section » (parties du document parcourues), ses reformulations et ses réussites aux questions du tuteur ; (2) le TUTORAT = ses besoins d'aide (« aide », « mot », « traduction », « question », « bouton »), qui montrent ses difficultés de langue ou de vocabulaire.
Les événements « quiz » sont les réponses au quiz facultatif de fin (kind = litteral, inference ou vocabulaire ; juste = réussite) : appuie-toi dessus pour « comprehension » et « vocabulaire » quand ils existent, sans les confondre avec le tutorat. Règles : décris seulement ce que les traces montrent ; n'invente rien ; « niveau_indicatif » est une estimation indicative (A1, A2, A2+, B1, B2 ou « indéterminé ») qui ne remplace PAS une évaluation ; mets dans "reserve" une phrase sur les limites de l'estimation (peu de données, aide du tuteur…). Les productions de l'élève dans sa langue première sont traduites en français : signale-les dans "traductions" comme « à vérifier ». Au maximum 3 recommandations concrètes, adaptées à la matière (${S.nom}) et au niveau. Écris pour un enseignant, en français clair.
Réponds UNIQUEMENT par un objet JSON : {"resume": string (2-3 phrases), "points_forts": [string], "difficultes": [string], "vocabulaire": {"acquis": [mots], "a_retravailler": [mots]}, "comprehension": {"litterale": string, "inference": string}, "production": {"observations": string, "erreurs_recurrentes": [string], "traductions": [{"texte": string (production dans la langue de l'élève), "fr": string (traduction)}]}, "travail": string (le travail de l'élève sur l'activité, ou sa compréhension de la lecture si c'est une ressource ; 2-3 phrases), "besoins_tutorat": string (ce que ses demandes d'aide révèlent ; 2 phrases), "autonomie": string, "niveau_indicatif": {"reception": string, "production": string, "reserve": string}, "recommandations": [string]}

Document : « ${String(titre).slice(0, 120)} »
Extrait du document :
${passages.slice(0, 40).map(p => String(p.t || '').slice(0, 160)).join('\n').slice(0, 2500)}

Chiffres calculés : ${JSON.stringify(stats)}

Traces (mm:ss, type, détails) :
${trace}`;
    const out = parseJson(await albert([{ role: 'system', content: sys }, { role: 'user', content: 'Rédige le bilan.' }]));
    res.json({ stats, analyse: normalizeReport(out) });
  } catch (e) { console.error(e); res.status(500).json({ error: e.message }); }
});

app.listen(process.env.PORT || 3000, () => {
  console.log(`Tuteur FLSco ${VERSION} : http://localhost:` + (process.env.PORT || 3000));
  console.log('Dossier :', process.cwd());
  console.log('Code d\'accès :', ACCESS_CODE ? 'activé' : 'désactivé' + (process.env.NODE_ENV === 'production' || process.env.RENDER ? '  ⚠ ATTENTION : définis ACCESS_CODE avant d\'ouvrir l\'application aux élèves' : ''));
  let ui = 'introuvable (public/index.html manquant)';
  try { ui = readFileSync('public/index.html', 'utf8').includes('Interface ' + VERSION) ? `à jour (${VERSION})` : `ANCIENNE VERSION : remplace public/index.html`; } catch {}
  console.log('Interface :', ui);
});
