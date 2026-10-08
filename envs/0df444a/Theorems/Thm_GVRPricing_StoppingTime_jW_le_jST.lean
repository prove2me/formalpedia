-- Prove2me | Theorems.Thm_GVRPricing_StoppingTime_jW_le_jST
-- name    : GVRPricing.StoppingTime.jW_le_jST
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:05:21.878412+00:00
-- url     : https://prove2.me/theorems/ef58ca84-2720-4dbf-aee6-c6802aa1465a
-- title:
--   Proof of Theorem 5 — the wasteful heuristic is a lower bound: $J^W(n,t)\le J^{ST}(n,t)$
-- statement:
--   Let $1\le k\le K-1$, $n\in\mathbb N$ and $t$ satisfy $\lambda_k t\ge n>\lambda_{k+1}t$. Then the expected revenue of the wasteful heuristic does not exceed that of the stopping-time heuristic:
--
--   $$J^W(n,t)\le J^{ST}(n,t).$$
--
--   The wasteful heuristic decouples the two price phases into independent Poisson counts, which is what makes its revenue computable; this inequality transfers its lower bound to the ST heuristic.
--
--   **Formalization Note** $J^{ST}$ is the expected revenue of the exponential-clock sales process under the ST policy, and $J^W$ is the paper's two-Poisson formula. Lean index `k` is the paper's $k$ minus one.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1018 (PDF 20), Appendix, Proof of Theorem 5, first paragraph

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_Wasteful

namespace GVRPricing.StoppingTime

/-- Appendix, Proof of Theorem 5 (p. 1018): the wasteful heuristic earns no more than the
stopping-time heuristic, `J^W(n, t) ≤ J^ST(n, t)`, for (0-based) `k` with `k + 1 < K` and
`λ_{k+1} t < n ≤ λ_k t`. -/
theorem jW_le_jST {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    jW M k n t ≤ jST M k n t := by sorry

end GVRPricing.StoppingTime
