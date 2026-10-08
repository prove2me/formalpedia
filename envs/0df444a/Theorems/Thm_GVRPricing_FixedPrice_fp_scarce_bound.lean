-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_fp_scarce_bound
-- name    : GVRPricing.FixedPrice.fp_scarce_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:00:18.090914+00:00
-- url     : https://prove2.me/theorems/986c1b7f-571e-4438-a72f-4eceea9da0f7
-- title:
--   Proof of Theorem 3, case λ*t > n — J^FP(n,t) ≥ np⁰(1 − 1/(2√n)) = r⁰t(1 − 1/(2√n))
-- statement:
--   Let $(\Lambda,p,\lambda^*)$ be a regular demand function, $n\ge1$ a stock and $t>0$ a horizon with $\lambda^*t>n$, the case in which items are scarce. The fixed-price heuristic then uses the run-out price $p^0=p(n/t)$, and with $r^0=r(n/t)$,
--   $$J^{FP}(n,t)\ \ge\ np^0\Big(1-\frac{1}{2\sqrt n}\Big)=r^0t\Big(1-\frac{1}{2\sqrt n}\Big).$$
--
--   This is one of the two cases of Theorem 3. Compared with $J^D(n,t)=r^0t$ (Proposition 2), it gives the ratio $1-1/(2\sqrt n)$.
--
--   **Formalization Note** $J^{FP}(n,t)$ is the expected revenue of the constant-price policy at $\lambda^D=\min\{\lambda^*,n/t\}=n/t$, in $[0,\infty]$; the bound is stated for its embedding. The hypothesis $n\ge1$ makes $1/(2\sqrt n)$ defined; $\lambda^*t>n$ with $n\ge1$ is the page's case.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1008 (PDF 10), §3.3, Proof of Theorem 3, display after (18)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Proof of Theorem 3, scarce case** (p. 1008). If `λ* t > n ≥ 1` (`t > 0`), the fixed-price
heuristic uses the run-out price `p⁰ = p(n/t)` and
`J^FP(n, t) ≥ n p⁰ (1 − 1/(2√n)) = r⁰ t (1 − 1/(2√n))` with `r⁰ = r(n/t)`. -/
theorem fp_scarce_bound (M : Model) (n : ℕ) (t : ℝ) (hn : 1 ≤ n) (ht : 0 < t)
    (h : (n : ℝ) < M.lstar * t) :
    ENNReal.ofReal (n * M.p (n / t) * (1 - 1 / (2 * Real.sqrt n))) ≤ fpValue M n t ∧
    n * M.p (n / t) * (1 - 1 / (2 * Real.sqrt n)) =
      M.r (n / t) * t * (1 - 1 / (2 * Real.sqrt n)) := by sorry

end GVRPricing.FixedPrice
