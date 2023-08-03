const balanced = require('balanced-match');
const {
  ArrayPrototypeJoin,
  ArrayPrototypeMap,
  ArrayPrototypePush,
  ArrayPrototypePushApply,
  ArrayPrototypeShift,
  ArrayPrototypeSome,
  RegExpPrototypeTest,
  MathAbs,
  MathMax,
  MathRandom,
  RegExpPrototypeSymbolMatch,
  String,
  StringFromCharCode,
  StringPrototypeCharCodeAt,
  StringPrototypeIndexOf,
  StringPrototypeSplit,
  StringPrototypeSlice,
} = require('node-primordials')

const escSlash = '\0SLASH'+MathRandom()+'\0';
const escOpen = '\0OPEN'+MathRandom()+'\0';
const escClose = '\0CLOSE'+MathRandom()+'\0';
const escComma = '\0COMMA'+MathRandom()+'\0';
const escPeriod = '\0PERIOD'+MathRandom()+'\0';

/**
 * @return {number}
 */
function numeric(str) {
  return parseInt(str, 10) == str
    ? parseInt(str, 10)
    : StringPrototypeCharCodeAt(str, 0);
}

/**
 * @param {string} str
 */
function escapeBraces(str) {
  return ArrayPrototypeJoin(StringPrototypeSplit(
    ArrayPrototypeJoin(StringPrototypeSplit(
        ArrayPrototypeJoin(StringPrototypeSplit(
          ArrayPrototypeJoin(StringPrototypeSplit(
            ArrayPrototypeJoin(StringPrototypeSplit(str, '\\\\'), escSlash),
          '\\{'), escOpen),
        '\\}'), escClose),
      '\\,'), escComma),
    '\\.'), escPeriod);
}

/**
 * @param {string} str
 */
function unescapeBraces(str) {
  return ArrayPrototypeJoin(StringPrototypeSplit(
    ArrayPrototypeJoin(StringPrototypeSplit(
        ArrayPrototypeJoin(StringPrototypeSplit(
          ArrayPrototypeJoin(StringPrototypeSplit(
            ArrayPrototypeJoin(StringPrototypeSplit(str, escSlash), '\\'),
          escOpen), '{'),
        escClose), '}'),
      escComma), ','),
    escPeriod), '.');
}

/**
 * Basically just str.split(","), but handling cases
 * where we have nested braced sections, which should be
 * treated as individual members, like {a,{b,c},d}
 * @param {string} str
 */
function parseCommaParts(str) {
  if (!str)
    return [''];

  const parts = [];
  const m = balanced('{', '}', str);

  if (!m)
    return StringPrototypeSplit(str, ',');

  const {pre, body, post} = m;
  const p = StringPrototypeSplit(pre, ',');

  p[p.length-1] += '{' + body + '}';
  const postParts = parseCommaParts(post);
  if (post.length) {
    p[p.length-1] += ArrayPrototypeShift(postParts);
    ArrayPrototypePushApply(p, postParts);
  }

  ArrayPrototypePushApply(parts, p);

  return parts;
}

/**
 * @param {string} str
 */
function expandTop(str) {
  if (!str)
    return [];

  // I don't know why Bash 4.3 does this, but it does.
  // Anything starting with {} will have the first two bytes preserved
  // but *only* at the top level, so {},a}b will not expand to anything,
  // but a{},b}c will be expanded to [a}c,abc].
  // One could argue that this is a bug in Bash, but since the goal of
  // this module is to match Bash's rules, we escape a leading {}
  if (StringPrototypeSlice(str, 0, 2) === '{}') {
    str = '\\{\\}' + StringPrototypeSlice(str, 2);
  }

  return ArrayPrototypeMap(expand(escapeBraces(str), true), unescapeBraces);
}

/**
 * @param {string} str
 */
function embrace(str) {
  return '{' + str + '}';
}

/**
 * @param {string} el
 */
function isPadded(el) {
  return RegExpPrototypeTest(/^-?0\d/, el);
}

/**
 * @param {number} i
 * @param {number} y
 */
function lte(i, y) {
  return i <= y;
}

/**
 * @param {number} i
 * @param {number} y
 */
function gte(i, y) {
  return i >= y;
}

/**
 * @param {string} str
 * @param {boolean} [isTop]
 */
function expand(str, isTop) {
  /** @type {string[]} */
  const expansions = [];

  const m = balanced('{', '}', str);
  if (!m) return [str];

  // no need to expand pre, since it is guaranteed to be free of brace-sets
  const pre = m.pre;
  const post = m.post.length
    ? expand(m.post, false)
    : [''];

  if (RegExpPrototypeTest(/\$$/, m.pre)) {
    for (let k = 0; k < post.length; k++) {
      const expansion = pre+ '{' + m.body + '}' + post[k];
      ArrayPrototypePush(expansions, expansion);
    }
  } else {
    const isNumericSequence =  RegExpPrototypeTest(/^-?\d+\.\.-?\d+(?:\.\.-?\d+)?$/, m.body);
    const isAlphaSequence =  RegExpPrototypeTest(/^[a-zA-Z]\.\.[a-zA-Z](?:\.\.-?\d+)?$/, m.body);
    const isSequence = isNumericSequence || isAlphaSequence;
    const isOptions = StringPrototypeIndexOf(m.body, ',') >= 0;
    if (!isSequence && !isOptions) {
      // {a},b}
      if (RegExpPrototypeSymbolMatch(/,.*\}/, m.post)) {
        str = m.pre + '{' + m.body + escClose + m.post;
        return expand(str);
      }
      return [str];
    }

    let n;
    if (isSequence) {
      n = StringPrototypeSplit(m.body, /\.\./);
    } else {
      n = parseCommaParts(m.body);
      if (n.length === 1) {
        // x{{a,b}}y ==> x{a}y x{b}y
        n = ArrayPrototypeMap(expand(n[0], false), embrace);
        if (n.length === 1) {
          return ArrayPrototypeMap(post, function(p) {
            return m.pre + n[0] + p;
          });
        }
      }
    }

    // at this point, n is the parts, and we know it's not a comma set
    // with a single entry.
    let N;

    if (isSequence) {
      const x = numeric(n[0]);
      const y = numeric(n[1]);
      const width = MathMax(n[0].length, n[1].length)
      let incr = n.length == 3
        ? MathAbs(numeric(n[2]))
        : 1;
      let test = lte;
      const reverse = y < x;
      if (reverse) {
        incr *= -1;
        test = gte;
      }
      const pad = ArrayPrototypeSome(n, isPadded);

      N = [];

      for (let i = x; test(i, y); i += incr) {
        let c;
        if (isAlphaSequence) {
          c = StringFromCharCode(i);
          if (c === '\\')
            c = '';
        } else {
          c = String(i);
          if (pad) {
            const need = width - c.length;
            if (need > 0) {
              const z = ArrayPrototypeJoin(new Array(need + 1), '0');
              if (i < 0)
                c = '-' + z + StringPrototypeSlice(c, 1);
              else
                c = z + c;
            }
          }
        }
        ArrayPrototypePush(N, c);
      }
    } else {
      N = [];

      for (let j = 0; j < n.length; j++) {
        ArrayPrototypePushApply(N, expand(n[j], false));
      }
    }

    for (let j = 0; j < N.length; j++) {
      for (let k = 0; k < post.length; k++) {
        const expansion = pre + N[j] + post[k];
        if (!isTop || isSequence || expansion)
          ArrayPrototypePush(expansions, expansion);
      }
    }
  }

  return expansions;
}

module.exports = expandTop;
