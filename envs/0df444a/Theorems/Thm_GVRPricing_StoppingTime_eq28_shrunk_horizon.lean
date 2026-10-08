-- Prove2me | Theorems.Thm_GVRPricing_StoppingTime_eq28_shrunk_horizon
-- name    : GVRPricing.StoppingTime.eq28_shrunk_horizon
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:47:18.092139+00:00
-- url     : https://prove2.me/theorems/407a1d91-60b4-4b4d-bf03-15b9252e82c0
-- title:
--   Equation (28) — the shrunk horizon satisfies $t-(\lambda_k-\lambda_{k+1})/(\lambda_k\lambda_{k+1})<t'\le t$
-- statement:
--   Let $1\le k\le K-1$, $n\in\mathbb N$ and $t$ satisfy $\lambda_k t\ge n>\lambda_{k+1}t$. Put $m=\lceil\lambda_k t_k\rceil$ with $t_k$ as in Proposition 4, $t_m=m/\lambda_k$, $t_{n-m}=(n-m)/\lambda_{k+1}$ and $t'=t_m+t_{n-m}$, the time needed to sell all $n$ items at deterministic rates. Then
--
--   $$t-\frac{\lambda_k-\lambda_{k+1}}{\lambda_k\lambda_{k+1}}<t'\le t.$$
--
--   So replacing the horizon by $t'$ loses at most a bounded amount of time, independent of $n$ and $t$.
--
--   **Formalization Note** The page prints $t_{n-m}\doteq n-m/\lambda_{k+1}$; the next sentence ("the time it takes to sell $n-m$ items at price $p_{k+1}$") shows that $(n-m)/\lambda_{k+1}$ is meant, and that is what is formalized. Lean index `k` is the paper's $k$ minus one.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1018 (PDF 20), Appendix, Proof of Theorem 5, eq. (28)

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_STHeuristic

namespace GVRPricing.StoppingTime

/-- Equation (28) (p. 1018): with `m = ⌈λ_k t_k⌉`, `t_m = m/λ_k`, `t_{n−m} = (n − m)/λ_{k+1}` and
`t' = t_m + t_{n−m}`, `t − (λ_k − λ_{k+1})/(λ_k λ_{k+1}) < t' ≤ t` (0-based `k`, `k + 1 < K`). -/
theorem eq28_shrunk_horizon {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K) (n : ℕ) (t : ℝ)
    (hup : (n : ℝ) ≤ M.lamN k * t) (hlow : M.lamN (k + 1) * t < n) :
    t - (M.lamN k - M.lamN (k + 1)) / (M.lamN k * M.lamN (k + 1)) < shrunkHorizon M k n t ∧
      shrunkHorizon M k n t ≤ t := by sorry

end GVRPricing.StoppingTime
