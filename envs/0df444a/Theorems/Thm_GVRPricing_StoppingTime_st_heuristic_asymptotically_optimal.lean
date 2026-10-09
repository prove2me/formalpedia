-- Prove2me | Theorems.Thm_GVRPricing_StoppingTime_st_heuristic_asymptotically_optimal
-- name    : GVRPricing.StoppingTime.st_heuristic_asymptotically_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:47:41.925091+00:00
-- url     : https://prove2.me/theorems/7f2f7f2c-4e15-4884-bb6e-ed7d7ea58b09
-- title:
--   Theorem 5 — with a discrete price set the two-price stopping-time heuristic is asymptotically optimal: $J^{ST}(n,t)/J^D(n,t)\to1$
-- statement:
--   Fix a menu of $K\ge 2$ prices and an index $k$ with $1\le k\le K-1$. Let $(n_j)$ be stocks in $\mathbb N$ and $(t_j)$ horizons with $t_j\to\infty$ and
--
--   $$\lambda_k t_j\ge n_j>\lambda_{k+1}t_j\qquad\text{for all }j.$$
--
--   Then the expected revenue of the stopping-time heuristic is asymptotically equal to the deterministic revenue:
--
--   $$\lim_{j\to\infty}\frac{J^{ST}(n_j,t_j)}{J^D(n_j,t_j)}=1.$$
--
--   Since $J^D$ bounds the optimal expected revenue from above (§4.0.1), the ST heuristic, which uses only two adjacent prices and switches once, is asymptotically optimal among all pricing policies with prices in the menu.
--
--   **Formalization Note** The paper's joint limit "$n\to\infty$ and $t\to\infty$ such that $\lambda_k t\ge n>\lambda_{k+1}t$" is read as: $k$ fixed, any sequences with $t_j\to\infty$ in that regime ($n_j\to\infty$ follows, since $\lambda_{k+1}>0$). The ratio $n_j/t_j$ may vary along the sequence, which is stronger than the subsequence the proof reduces to. The edge cases $k=0$ and $k=K$, where the heuristic is a fixed-price policy, are excluded; the page treats them only in an unproved remark. Lean index `k` is the paper's $k$ minus one; the menu includes the concavity condition, without which the theorem is false.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1011 (PDF 13), Theorem 5; proof in the Appendix, p. 1018 (PDF 20)

import Mathlib
import Definitions.Def_GVRPricing_StoppingTime_DetLP
import Definitions.Def_GVRPricing_StoppingTime_STHeuristic

open Filter Topology

namespace GVRPricing.StoppingTime

/-- Theorem 5 (p. 1011): the stopping-time heuristic is asymptotically optimal.  Fix a menu and a
(0-based) index `k` with `k + 1 < K` (the paper's `1 ≤ k ≤ K − 1`).  Along any sequences of stocks
`n_j` and horizons `t_j → ∞` with `λ_k t_j ≥ n_j > λ_{k+1} t_j`, `J^ST(n_j, t_j)/J^D(n_j, t_j) → 1`. -/
theorem st_heuristic_asymptotically_optimal {K : ℕ} (M : Menu K) (k : ℕ) (hk : k + 1 < K)
    (n : ℕ → ℕ) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop)
    (hreg : ∀ j, (n j : ℝ) ≤ M.lamN k * t j ∧ M.lamN (k + 1) * t j < n j) :
    Tendsto (fun j => jST M k (n j) (t j) / detValue M (n j) (t j)) atTop (𝓝 1) := by sorry

end GVRPricing.StoppingTime
