-- Prove2me | Theorems.Thm_NondualOpt_fact_29
-- name    : NondualOpt.fact_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:36.321939+00:00
-- url     : https://prove2.me/theorems/8c63f286-f119-4a66-994e-64cb02b76428
-- title:
--   Fact 29 — covering numbers of $\ell_p$ balls by $\ell_s$ balls
-- statement:
--   For $1\le p,s\le\infty$, $d\ge1$ and $R>0$,
--   $$
--   \log N(B_p^d,R\,B_s^d)\lesssim_{p,s}d\Big(1+\log_+\frac{d^{1/s-1/p}}R\Big),\tag{22}
--   $$
--   and for $1\le p<s\le2$ and $0<R<1$,
--   $$
--   \log N(B_p^d,R\,B_s^d)\lesssim_{p,s}R^{-1/(1/p-1/s)}\log\frac{Ced}R .\tag{23}
--   $$
--   (22) is the packing–volume bound and (23) Schütt's intermediate entropy estimate; both are classical results the paper cites. Together with Proposition 28 they give Theorem 30.
--
--   Differences from the source:
--   - reading: the constant C inside log(Ced/R) → a second constant C' depending on (p, s), next to the outer constant; reason: the page uses a generic constant
--   - encoding: ≲_{p,s}, log_+, d ∈ ℕ → constants depending only on (p, s) chosen before d and R; log_+ t = max(log t, 0); d ≥ 1; values in [0, ∞]; reason: definitions on p.6–7
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Fact 29, (22)–(23), p.39

import Mathlib
import Definitions.Def_NondualOpt_coverNum
import Definitions.Def_NondualOpt_logN

open scoped ENNReal

namespace NondualOpt

/-- **Fact 29 (Covering numbers).** For `1 ≤ p, s ≤ ∞` and `R > 0`,
`log N(B_p^d, R B_s^d) ≲_{p,s} d(1 + log₊(d^{1/s − 1/p}/R))` (22), and
`log N(B_p^d, R B_s^d) ≲_{p,s} R^{−1/(1/p − 1/s)} log(Ced/R)` for `1 ≤ p < s ≤ 2`, `0 < R < 1` (23).
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Fact 29, (22)–(23), p.39.

**Formalization Note.** `≲_{p,s}` is a constant depending only on `(p, s)`, chosen before `d` and
`R`; the constant `C` inside `log(Ced/R)` is a second such constant `C'`. `log₊ t = max(log t, 0)`;
`1/∞ = 0`. `d ≥ 1`. Values in `ℝ≥0∞`. -/
theorem fact_29 :
    (∀ p s : ℝ≥0∞, 1 ≤ p → 1 ≤ s → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ R : ℝ, 0 < R →
      logN (coverNum p s d R) ≤ ENNReal.ofReal (C * d *
        (1 + max 0 (Real.log ((d : ℝ) ^ (s⁻¹.toReal - p⁻¹.toReal) / R))))) ∧
    (∀ p s : ℝ≥0∞, 1 ≤ p → p < s → s ≤ 2 → ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ d : ℕ, 1 ≤ d → ∀ R : ℝ, 0 < R → R < 1 →
        logN (coverNum p s d R) ≤ ENNReal.ofReal (C * R ^ (-1 / (p⁻¹.toReal - s⁻¹.toReal)) *
          Real.log (C' * Real.exp 1 * d / R))) := by sorry

end NondualOpt
