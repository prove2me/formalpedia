-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_optValue_le_detValue
-- name    : GVRPricing.FixedPrice.optValue_le_detValue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:03:53.7308+00:00
-- url     : https://prove2.me/theorems/8d34b533-86cf-47c8-91e0-7f5674db1d8c
-- title:
--   Theorem 2 — the deterministic revenue bounds the optimal expected revenue: J*(n,t) ≤ J^D(n,t)
-- statement:
--   Let $\lambda(p)$ be a regular demand function. For every stock $0\le n<\infty$ and every horizon $0\le t<\infty$,
--   $$J^*(n,t)\le J^D(n,t),$$
--   where $J^*(n,t)=\sup_{u\in\mathcal U}J_u(n,t)$ is the optimal expected revenue of the stochastic pricing problem (7) and $J^D(n,t)$ the optimal value of the deterministic problem (11) with stock $x=n$.
--
--   Uncertainty in sales can only lower the expected revenue. The bound gives every heuristic a computable benchmark, and Theorem 3 uses it to measure the fixed-price heuristic.
--
--   **Formalization Note** $J^*$ is the supremum over all non-anticipating policies, in $[0,\infty]$, and $J^D(n,t)$ is embedded in $[0,\infty]$. The boundary cases $n=0$ and $t=0$, which the page includes, are included.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1007 (PDF 9), §3.2.1, Theorem 2

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess
import Definitions.Def_GVRPricing_FixedPrice_Deterministic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Theorem 2** (p. 1007). If `λ(p)` is a regular demand function, then for every stock
`0 ≤ n < ∞` and horizon `0 ≤ t < ∞`, `J*(n, t) ≤ J^D(n, t)`: the optimal expected revenue of
the stochastic problem (7) is at most the optimal value of the deterministic problem (11) with
`x = n`. -/
theorem optValue_le_detValue (M : Model) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    optValue M n t ≤ ENNReal.ofReal (detValue M n t) := by sorry

end GVRPricing.FixedPrice
