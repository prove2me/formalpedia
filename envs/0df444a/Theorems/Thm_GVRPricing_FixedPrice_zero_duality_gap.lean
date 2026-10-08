-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_zero_duality_gap
-- name    : GVRPricing.FixedPrice.zero_duality_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:03:43.885649+00:00
-- url     : https://prove2.me/theorems/82f0adc1-ba3a-40a1-8e4c-40e1eae42494
-- title:
--   Proof of Theorem 2 — zero duality gap: J^D(n,t) = inf_{μ≥0} J^D(n,t,μ) = J^D(n,t,μ*)
-- statement:
--   Let $(\Lambda,p,\lambda^*)$ be a regular demand function, $n>0$ a stock and $t>0$ a horizon. Then there is a multiplier $\mu^*\ge0$ such that
--   $$J^D(n,t)=\inf_{\mu\ge0}J^D(n,t,\mu)=J^D(n,t,\mu^*).$$
--
--   The deterministic problem (11) is a convex program with the strictly feasible null path $\lambda\equiv0$, and its Lagrangian dual has no duality gap. This is the last step of the proof of Theorem 2: combined with Lemma 1 and (15), it turns $J^*(n,t)\le\inf_\mu J^D(n,t,\mu)$ into $J^*(n,t)\le J^D(n,t)$.
--
--   **Formalization Note** The statement says that $J^D(n,t)$ is the least element of $\{J^D(n,t,\mu):\mu\ge0\}$, which asserts both the equality with the infimum and its attainment.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1007 (PDF 9), §3.2.1, Proof of Theorem 2, final paragraph (unnumbered)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_Deterministic

open MeasureTheory Set

namespace GVRPricing.FixedPrice

/-- **Zero duality gap** (§3.2.1, end of the Proof of Theorem 2, p. 1007). For a stock `n > 0` and
a horizon `t > 0` there is a multiplier `μ* ≥ 0` with
`J^D(n, t) = inf_{μ ≥ 0} J^D(n, t, μ) = J^D(n, t, μ*)`: `J^D(n, t)` is the least value of
`μ ↦ J^D(n, t, μ)` over `μ ≥ 0`, and it is attained. -/
theorem zero_duality_gap (M : Model) (n : ℕ) (t : ℝ) (hn : 0 < n) (ht : 0 < t) :
    IsLeast ((fun μ => detAugValue M n t μ) '' Ici 0) (detValue M n t) := by sorry

end GVRPricing.FixedPrice
