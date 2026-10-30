-- Prove2me | Theorems.Thm_KUMultimodular_log_rPrime_le
-- name    : KUMultimodular.log_rPrime_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:04:04.607471+00:00
-- url     : https://prove2.me/theorems/19190b6a-0adc-454a-b02a-5c08e54c10db
-- title:
--   Estimate (4.1): $\log r' \le O(ed^2m^2(\log e+\log r)) \le O(\log q\log\log q)\,d^2m^2$ (corrected: first step)
-- statement:
--   There is a constant $C > 0$ such that for all $r, e, d \in \mathbb N$ and $m \ge 1$, with
--   $$M = d^m (e(r-1))^{(d-1)m+1} + 1, \qquad r' = M^{(e-1)dm+1}, \qquad q = r^e,$$
--   all three of
--   $$\log_2 r' \le \bigl((e-1)dm+1\bigr)\log_2 M, \qquad \log_2 r' \le C\, e\, d^2 m^2 \bigl(\lg e + \lg r\bigr) \qquad\text{and}\qquad \log_2 r' \le C\, \lg q \cdot \lg\lg q \cdot d^2 m^2$$
--   hold, where $\lg x = \max(1, \log_2 x)$.
--
--   Algorithm MULTIMODULAR-FOR-EXTENSION-RING runs MULTIMODULAR over $\mathbb Z/r'\mathbb Z$; this estimate converts the running time of Theorem 4.2 in terms of $\log r'$ into the running time of Theorem 4.4 in terms of $\log q$.
--
--   **Formalization Note** $M$ and $r'$ are `bigM r e m d` and `rPrime r e m d`, with truncated $e-1$, $d-1$, $r-1$.
--
--   Differences from the source:
--   - correction: log r′ = log(M^{(e−1)(d−1)m+1}) ⩽ (e − 1)dm log(d^m(e(r − 1))^{(d−1)m+1} + 1) → log₂ r′ ≤ ((e−1)dm + 1) log₂ M; reason: the printed first inequality is false for e = 1: r = 3, e = 1, d = m = 1 give M = 3, r' = 3 and log r' = log 3 > 0 = (e − 1)dm log M; the factor (e−1)dm + 1 is the exponent of r′, and the two later bounds of the chain hold as printed
--   - reading: r′ = M^{(e−1)(d−1)m+1} (p. 16) → r′ = M^{(e−1)dm+1} (p. 15); reason: p. 16's exponent is a typo: with it Step 4 of the algorithm has too few base-M digits when e ≥ 2; the r' of p. 15 is the one the algorithm uses, and the bound for it implies the bound for the smaller p. 16 value
--   - encoding: O(·), log → explicit C > 0 uniform in r, e, d, m; log₂ on the left, lg = max(1, log₂) on the right; reason: the meaning of the asymptotic notation; the clipping only keeps log e, log log q from being 0 or negative (e = 1, q ≤ 2)
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), estimate (4.1), proof of Theorem 4.4, p. 16

import Mathlib
import Definitions.Def_KUMultimodular_lam
import Definitions.Def_KUMultimodular_multimodularExt

namespace KUMultimodular

/-- **Estimate (4.1)** (Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008), p. 16), the
whole chain `log r' ≤ ((e-1)dm + 1) log M ≤ O(e d^2 m^2 (log e + log r)) ≤ O(log q log log q) d^2 m^2`,
where `r' = M^{(e-1)dm+1}`, `M = d^m (e(r-1))^{(d-1)m+1} + 1` and `q = r^e`. The first step is
corrected: the page has the factor `(e-1)dm`, which is false for `e = 1`. There is a constant
`C > 0` such that for all `r, e, d` and `m ≥ 1`,
`log₂ r' ≤ ((e-1)dm+1) log₂ M`, `log₂ r' ≤ C · e d^2 m^2 (log e + log r)` and
`log₂ r' ≤ C · log q · log log q · d^2 m^2`
(the logarithms on the right of the last two base 2, clipped below at `1`). -/
theorem log_rPrime_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (r e d m : ℕ), 1 ≤ m →
      Real.logb 2 (rPrime r e m d) ≤
              (((e - 1) * d * m + 1 : ℕ) : ℝ) * Real.logb 2 (bigM r e m d) ∧
        Real.logb 2 (rPrime r e m d) ≤
          C * e * (d : ℝ) ^ 2 * (m : ℝ) ^ 2 * (lg e + lg r) ∧
        Real.logb 2 (rPrime r e m d) ≤
          C * lg ((r : ℝ) ^ e) * lg (lg ((r : ℝ) ^ e)) * (d : ℝ) ^ 2 * (m : ℝ) ^ 2 := by sorry

end KUMultimodular
