-- Prove2me | Theorems.Thm_GVRPricing_StoppingTime_eq29_ratio_chain
-- name    : GVRPricing.StoppingTime.eq29_ratio_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:05:54.541794+00:00
-- url     : https://prove2.me/theorems/0a681cb4-6add-4d24-ab96-f59f1df88b9b
-- title:
--   Equation (29) — $J^{ST}/J^D\ge J^W(n,t)/J^D(n,t)\ge J^W(n,t')/(J^D(n,t')+(p_{k+1}-p_k))$
-- statement:
--   Let $1\le k\le K-1$, $n\in\mathbb N$ and $t$ satisfy $\lambda_k t\ge n>\lambda_{k+1}t$, and let $t'$ be the shrunk horizon of (28). Then
--
--   $$\frac{J^{ST}(n,t)}{J^D(n,t)}\ge\frac{J^W(n,t)}{J^D(n,t)}\ge\frac{J^W(n,t')}{J^D(n,t')+(p_{k+1}-p_k)}.$$
--
--   This chain reduces Theorem 5 to an estimate of the wasteful heuristic at the shrunk horizon, where the stock allocated to each price equals its deterministic sales.
--
--   **Formalization Note** The paper's (29) has $J^{ST}(n,t)/J^*(n,t)$ on the left, with $J^*$ the optimal expected revenue over all non-anticipating policies. $J^*$ is not defined in this mission, so the left ratio uses $J^D$ instead; since $J^*\le J^D$ (§4.0.1), this left inequality implies the paper's. $J^W(n,t')$ is the wasteful heuristic computed at horizon $t'$; its $m$ coincides with the one at horizon $t$. Lean index `k` is the paper's $k$ minus one.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1018 (PDF 20), Appendix, Proof of Theorem 5, eq. (29)

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_DetLP
import Definitions.Def_GVRPricing_StoppingTime_Wasteful

namespace GVRPricing.StoppingTime

/-- Equation (29) (p. 1018), with `J^D` in place of `J*` in the leftmost ratio:
`J^ST(n, t)/J^D(n, t) ≥ J^W(n, t)/J^D(n, t) ≥ J^W(n, t')/(J^D(n, t') + (p_{k+1} − p_k))`,
for (0-based) `k` with `k + 1 < K` and `λ_{k+1} t < n ≤ λ_k t`; `t'` is the shrunk horizon. -/
theorem eq29_ratio_chain {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    jW M k n t / detValue M n t ≤ jST M k n t / detValue M n t ∧
      jW M k n (shrunkHorizon M k n t)
          / (detValue M n (shrunkHorizon M k n t) + (M.pN (k + 1) - M.pN k))
        ≤ jW M k n t / detValue M n t := by sorry

end GVRPricing.StoppingTime
