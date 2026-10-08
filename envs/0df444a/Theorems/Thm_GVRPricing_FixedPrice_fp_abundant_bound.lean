-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_fp_abundant_bound
-- name    : GVRPricing.FixedPrice.fp_abundant_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:00:22.155093+00:00
-- url     : https://prove2.me/theorems/dca93b53-cce7-47fc-88a2-5461ea8f6cda
-- title:
--   Eq. (19) — case λ*t ≤ n: J^FP(n,t) ≥ p*(λ*t − (√(λ*t + (n − λ*t)²) − (n − λ*t))/2) ≥ r*t(1 − 1/(2√(λ*t)))
-- statement:
--   Let $(\Lambda,p,\lambda^*)$ be a regular demand function with $\lambda^*>0$, $n$ a stock and $t>0$ a horizon with $\lambda^*t\le n$, the case in which items are plentiful. The fixed-price heuristic then prices at $p^*=p(\lambda^*)$, and
--   $$J^{FP}(n,t)\ \ge\ p^*\Big(\lambda^*t-\frac{\sqrt{\lambda^*t+(n-\lambda^*t)^2}-(n-\lambda^*t)}{2}\Big)\ \ge\ p^*\lambda^*t\Big(1-\frac{1}{2\sqrt{\lambda^*t}}\Big)=r^*t\Big(1-\frac{1}{2\sqrt{\lambda^*t}}\Big).\qquad(19)$$
--
--   This is the second case of Theorem 3. Compared with $J^D(n,t)=r^*t$ (Proposition 2), it gives the ratio $1-1/(2\sqrt{\lambda^*t})$.
--
--   **Formalization Note** The first inequality is stated for the embedding of a real number into $[0,\infty]$; the other two are inequalities of real numbers. The hypothesis $\lambda^*>0$ makes $1/(2\sqrt{\lambda^*t})$ defined; it is also a hypothesis of the goal theorem.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1008 (PDF 10), §3.3, Proof of Theorem 3, eq. (19)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Proof of Theorem 3, abundant case, eq. (19)** (p. 1008). If `λ* t ≤ n` (`t > 0`, `λ* > 0`),
the fixed-price heuristic uses `p* = p(λ*)` and
`J^FP(n, t) ≥ p*(λ*t − (√(λ*t + (n − λ*t)²) − (n − λ*t))/2) ≥ p*λ*t(1 − 1/(2√(λ*t)))
= r* t (1 − 1/(2√(λ*t)))`. -/
theorem fp_abundant_bound (M : Model) (n : ℕ) (t : ℝ) (ht : 0 < t) (hl : 0 < M.lstar)
    (h : M.lstar * t ≤ n) :
    ENNReal.ofReal (M.pstar * (M.lstar * t -
        (Real.sqrt (M.lstar * t + ((n : ℝ) - M.lstar * t) ^ 2) - ((n : ℝ) - M.lstar * t)) / 2))
      ≤ fpValue M n t ∧
    M.pstar * M.lstar * t * (1 - 1 / (2 * Real.sqrt (M.lstar * t))) ≤
      M.pstar * (M.lstar * t -
        (Real.sqrt (M.lstar * t + ((n : ℝ) - M.lstar * t) ^ 2) - ((n : ℝ) - M.lstar * t)) / 2) ∧
    M.pstar * M.lstar * t * (1 - 1 / (2 * Real.sqrt (M.lstar * t))) =
      M.rstar * t * (1 - 1 / (2 * Real.sqrt (M.lstar * t))) := by sorry

end GVRPricing.FixedPrice
