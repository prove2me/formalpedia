-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_constant_policy_revenue
-- name    : GVRPricing.FixedPrice.constant_policy_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:00:22.473627+00:00
-- url     : https://prove2.me/theorems/5885bdc2-181f-4799-bf4e-26b8bb6b3bde
-- title:
--   Eq. (17) — fixing the price at p earns pE[N − (N − n)⁺], N Poisson with mean λ(p)t
-- statement:
--   Let $c\in\Lambda$, $c>0$, be an allowable rate with price $p=p(c)$, let $n$ be the stock and $t\ge0$ the horizon. The policy that charges the fixed price $p$ for the whole horizon (until the stock runs out) has expected revenue
--   $$p\,E\big[N_{\lambda(p)t}-(N_{\lambda(p)t}-n)^+\big]=p\,E\big[\min\{n,N_{\lambda(p)t}\}\big],\qquad(17)$$
--   where $N_{\lambda(p)t}$ is a Poisson random variable with mean $\lambda(p)t=ct$ and $x^+=\max(x,0)$.
--
--   The formula reduces the fixed-price heuristic to a computation with a Poisson distribution. It is the starting point of both case bounds in the proof of Theorem 3.
--
--   **Formalization Note** The left-hand side is the expected revenue of the constant-intensity policy built in the sales-process definition, not a formula. The Poisson law is Mathlib's `poissonMeasure` with rate $ct$, and the expectation is a lower Lebesgue integral of a nonnegative function.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1008 (PDF 10), §3.3, Proof of Theorem 3, eq. (17)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Eq. (17)** (§3.3, Proof of Theorem 3, p. 1008). For an allowable rate `c ∈ Λ`, `c > 0`, the
expected revenue of fixing the price at `p = p(c)` for the whole horizon `[0, t]`, from stock
`n`, is `p E[N − (N − n)⁺]` with `N` a Poisson random variable of mean `c t`. -/
theorem constant_policy_revenue (M : Model) (c : ℝ) (hc : c ∈ M.Λ) (hc0 : 0 < c) (n : ℕ) (t : ℝ)
    (ht : 0 ≤ t) :
    (constPolicy M c).expectedRevenue n t =
      ENNReal.ofReal (M.p c) *
        ∫⁻ k, ENNReal.ofReal ((k : ℝ) - max ((k : ℝ) - n) 0) ∂poissonMeasure (Real.toNNReal (c * t)) := by sorry

end GVRPricing.FixedPrice
