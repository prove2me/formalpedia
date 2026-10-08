-- Prove2me | Theorems.Thm_GVRPricing_StoppingTime_detValue_shrunk_bound
-- name    : GVRPricing.StoppingTime.detValue_shrunk_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:47:26.480067+00:00
-- url     : https://prove2.me/theorems/66ba6e10-529f-44c3-98ec-d9d1880355bb
-- title:
--   Proof of Theorem 5 — closed form of $J^D(n,t)$ and $J^D(n,t)<J^D(n,t')+(p_{k+1}-p_k)$
-- statement:
--   Let $1\le k\le K-1$, $n\in\mathbb N$ and $t$ satisfy $\lambda_k t\ge n>\lambda_{k+1}t$, and let $t'$ be the shrunk horizon of (28). Then the deterministic revenue is
--
--   $$J^D(n,t)=\frac{r_k-r_{k+1}}{\lambda_k-\lambda_{k+1}}\,n+\frac{\lambda_k r_{k+1}-\lambda_{k+1}r_k}{\lambda_k-\lambda_{k+1}}\,t,$$
--
--   and
--
--   $$J^D(n,t)<J^D(n,t')+(p_{k+1}-p_k).$$
--
--   Shrinking the horizon to $t'$ therefore costs the deterministic benchmark less than one price difference.
--
--   **Formalization Note** $J^D$ is the value of the LP of §4.0.1. Lean index `k` is the paper's $k$ minus one.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1018 (PDF 20), Appendix, Proof of Theorem 5, display after (28)

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_DetLP
import Definitions.Def_GVRPricing_StoppingTime_STHeuristic

namespace GVRPricing.StoppingTime

/-- Appendix, Proof of Theorem 5 (p. 1018), display after (28): for (0-based) `k` with `k + 1 < K`
and `λ_{k+1} t < n ≤ λ_k t`,
`J^D(n, t) = (r_k − r_{k+1})/(λ_k − λ_{k+1}) · n + (λ_k r_{k+1} − λ_{k+1} r_k)/(λ_k − λ_{k+1}) · t`,
and `J^D(n, t) < J^D(n, t') + (p_{k+1} − p_k)` with `t'` the shrunk horizon. -/
theorem detValue_shrunk_bound {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    detValue M n t =
        (M.rN k - M.rN (k + 1)) / (M.lamN k - M.lamN (k + 1)) * n
          + (M.lamN k * M.rN (k + 1) - M.lamN (k + 1) * M.rN k) / (M.lamN k - M.lamN (k + 1)) * t ∧
      detValue M n t < detValue M n (shrunkHorizon M k n t) + (M.pN (k + 1) - M.pN k) := by sorry

end GVRPricing.StoppingTime
