-- Prove2me | Theorems.Thm_MDPComplexity_AverageCost_closed_walk_mean
-- name    : MDPComplexity.AverageCost.closed_walk_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:58:31.659029+00:00
-- url     : https://prove2.me/theorems/0b257171-2366-42bc-bf91-4f8bde337841
-- title:
--   Closed walks of at most n arcs recover the least cycle mean
-- statement:
--   Let $n=|S|$, and let $C_0$ be a reachable simple cycle with least mean among all reachable simple cycles. Compare every closed decision walk of length $1\leq k\leq n$ based at a state reachable from $s_0$. Its cost divided by $k$ cannot be smaller than the mean of $C_0$, and some such closed walk attains equality:
--
--   $$\operatorname{mean}(C_0)=\min_{\substack{u\text{ reachable from }s_0\\1\leq k\leq n\\W:u\to u,\ |W|=k}}\frac{c(W)}{k}.$$
--
--   This justifies comparing the shortest closed walks of bounded lengths, even though a matrix power ranges over walks that may repeat states.
--
--   **Formalization Note** The paper numbers lengths from $1$ to $n$; the Lean bound is inclusive. A closed walk records decisions and can use loops or parallel arcs.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 446, §3 The infinite horizon undiscounted case, proof of Theorem 3, https://doi.org/10.1287/moor.12.3.441

import Definitions.Def_MDPComplexity_AverageCost_Model

namespace MDPComplexity.AverageCost

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- §3, p. 446: comparing closed walks with lengths 1 through n gives
the least mean of a reachable simple cycle. -/
theorem closed_walk_mean (M : DetMDP S) (s₀ : S) :
    ∀ C₀ : M.Cycle, M.Reachable s₀ C₀.base →
      (∀ C : M.Cycle, M.Reachable s₀ C.base → C₀.mean ≤ C.mean) →
      IsLeast {μ : ℝ | ∃ (u : S) (k : ℕ) (W : M.Walk k),
        M.Reachable s₀ u ∧ 1 ≤ k ∧ k ≤ Fintype.card S ∧
        W.start = u ∧ W.finish = u ∧ μ = W.cost / k} C₀.mean := by sorry

end MDPComplexity.AverageCost
