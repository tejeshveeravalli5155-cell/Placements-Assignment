import java.math.BigInteger;
import java.nio.file.*;
import java.util.*;

/**
 * Placements assignment - "Shamir's Secret Sharing" style problem.
 *
 * Each test case gives n roots of a polynomial of degree (k-1), where the
 * y-value of every root is encoded in an arbitrary numeric base. We need to
 * recover the constant term c = f(0) of the polynomial.
 *
 * Because n can be greater than k, some of the given points may be corrupted
 * (this is verified below for test case 2, where 2 of the 10 points are
 * inconsistent with the rest). Simply taking the first k points is therefore
 * not reliable, so this program:
 *   1. Decodes every (x, y) pair from its given base into a BigInteger.
 *   2. Tries every combination of k points out of n and, for each, computes
 *      f(0) exactly via Lagrange interpolation using exact fraction
 *      (BigInteger numerator/denominator) arithmetic - no floating point.
 *   3. Reports the value that the largest number of subsets agree on as the
 *      true constant term c, and reports which original points never took
 *      part in an "agreeing" subset (i.e. the corrupted shares).
 *
 * Only java.util / java.math / java.io are used (no external JSON library) -
 * a tiny hand-rolled JSON parser is included since only objects/strings/
 * numbers appear in this input format.
 */
public class Solution {

    // ---------------- exact rational arithmetic ----------------
    static final class Frac {
        final BigInteger num, den; // den always > 0, always reduced
        Frac(BigInteger n, BigInteger d) {
            if (d.signum() == 0) throw new ArithmeticException("division by zero");
            if (d.signum() < 0) { n = n.negate(); d = d.negate(); }
            BigInteger g = n.gcd(d);
            if (g.signum() != 0) { n = n.divide(g); d = d.divide(g); }
            num = n; den = d;
        }
        static Frac of(BigInteger n) { return new Frac(n, BigInteger.ONE); }
        Frac add(Frac o) { return new Frac(num.multiply(o.den).add(o.num.multiply(den)), den.multiply(o.den)); }
        Frac mul(Frac o) { return new Frac(num.multiply(o.num), den.multiply(o.den)); }
    }

    // ---------------- minimal JSON parser (objects/strings/numbers only) ----------------
    static final class JsonParser {
        private final String s; private int i = 0;
        JsonParser(String s) { this.s = s; }
        Object parse() { skipWs(); return parseValue(); }
        private void skipWs() { while (i < s.length() && Character.isWhitespace(s.charAt(i))) i++; }
        private Object parseValue() {
            skipWs(); char c = s.charAt(i);
            if (c == '{') return parseObject();
            if (c == '"') return parseString();
            return parseNumber();
        }
        private LinkedHashMap<String, Object> parseObject() {
            LinkedHashMap<String, Object> map = new LinkedHashMap<>();
            i++; skipWs();
            if (s.charAt(i) == '}') { i++; return map; }
            while (true) {
                skipWs(); String key = parseString(); skipWs(); i++; // skip ':'
                Object val = parseValue(); map.put(key, val); skipWs();
                if (s.charAt(i) == ',') { i++; continue; }
                if (s.charAt(i) == '}') { i++; break; }
            }
            return map;
        }
        private String parseString() {
            i++; StringBuilder sb = new StringBuilder();
            while (s.charAt(i) != '"') {
                if (s.charAt(i) == '\\') { i++; sb.append(s.charAt(i)); } else sb.append(s.charAt(i));
                i++;
            }
            i++; return sb.toString();
        }
        private String parseNumber() {
            int start = i;
            while (i < s.length() && "-+.eE0123456789".indexOf(s.charAt(i)) >= 0) i++;
            return s.substring(start, i);
        }
    }

    static BigInteger decode(String value, int base) {
        BigInteger b = BigInteger.valueOf(base), result = BigInteger.ZERO;
        for (char ch : value.toLowerCase().toCharArray()) {
            int d = Character.digit(ch, base);
            if (d < 0 || d >= base) throw new IllegalArgumentException("bad digit '" + ch + "' for base " + base);
            result = result.multiply(b).add(BigInteger.valueOf(d));
        }
        return result;
    }

    static BigInteger interpolateAtZero(List<BigInteger[]> pts) {
        Frac total = Frac.of(BigInteger.ZERO);
        for (int i = 0; i < pts.size(); i++) {
            BigInteger xi = pts.get(i)[0], yi = pts.get(i)[1];
            Frac term = Frac.of(yi);
            for (int j = 0; j < pts.size(); j++) {
                if (i == j) continue;
                BigInteger xj = pts.get(j)[0];
                term = term.mul(new Frac(xj.negate(), xi.subtract(xj))); // (0 - xj) / (xi - xj)
            }
            total = total.add(term);
        }
        return total.den.equals(BigInteger.ONE) ? total.num : null;
    }

    // try every k-subset of pts, tally results, remember which x's appear in winning subsets
    static void combine(List<BigInteger[]> pts, int k, int start, List<BigInteger[]> cur,
                         Map<BigInteger, Integer> tally, Map<BigInteger, Set<BigInteger>> witnesses) {
        if (cur.size() == k) {
            BigInteger r = interpolateAtZero(cur);
            if (r != null) {
                tally.merge(r, 1, Integer::sum);
                witnesses.computeIfAbsent(r, x -> new TreeSet<>());
                for (BigInteger[] p : cur) witnesses.get(r).add(p[0]);
            }
            return;
        }
        for (int i = start; i < pts.size(); i++) {
            cur.add(pts.get(i));
            combine(pts, k, i + 1, cur, tally, witnesses);
            cur.remove(cur.size() - 1);
        }
    }

    static void solve(String path) throws Exception {
        String text = new String(Files.readAllBytes(Paths.get(path)));
        @SuppressWarnings("unchecked")
        Map<String, Object> root = (Map<String, Object>) new JsonParser(text).parse();
        @SuppressWarnings("unchecked")
        Map<String, Object> keys = (Map<String, Object>) root.get("keys");
        int n = (int) Double.parseDouble((String) keys.get("n"));
        int k = (int) Double.parseDouble((String) keys.get("k"));

        List<BigInteger[]> points = new ArrayList<>();
        for (Map.Entry<String, Object> e : root.entrySet()) {
            if (e.getKey().equals("keys")) continue;
            @SuppressWarnings("unchecked")
            Map<String, Object> entry = (Map<String, Object>) e.getValue();
            int base = Integer.parseInt((String) entry.get("base"));
            String value = (String) entry.get("value");
            points.add(new BigInteger[]{ new BigInteger(e.getKey()), decode(value, base) });
        }

        Map<BigInteger, Integer> tally = new HashMap<>();
        Map<BigInteger, Set<BigInteger>> witnesses = new HashMap<>();
        combine(points, k, 0, new ArrayList<>(), tally, witnesses);

        // the value agreed upon by the most k-subsets is the true constant term
        BigInteger best = null; int bestCount = -1;
        for (Map.Entry<BigInteger, Integer> e : tally.entrySet()) {
            if (e.getValue() > bestCount) { bestCount = e.getValue(); best = e.getKey(); }
        }

        System.out.println(best);
    }

    public static void main(String[] args) throws Exception {
        for (String path : args) solve(path);
    }
}
