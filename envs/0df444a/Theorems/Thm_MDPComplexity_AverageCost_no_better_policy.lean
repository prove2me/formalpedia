-- Prove2me | Theorems.Thm_MDPComplexity_AverageCost_no_better_policy
-- name    : MDPComplexity.AverageCost.no_better_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:57:56.418206+00:00
-- url     : https://prove2.me/theorems/3b582b0a-1169-4970-aaba-61cad5edccfb
-- title:
--   No policy improves on the least reachable cycle mean
-- statement:
--   Let $C_0$ be a reachable simple cycle of least mean cost among all reachable simple cycles of a finite stationary deterministic process. For every state-and-time policy $\delta$, even if its finite averages fail to converge,
--
--   $$\operatorname{mean}(C_0)\leq\liminf_{T\to\infty}\frac{1}{T}\sum_{t=0}^{T}c(s_t,\delta(s_t,t)).$$
--
--   This gives the lower-bound half of the cycle characterization, including arbitrary nonstationary policies.
--
--   **Formalization Note** The paper's phrase “this cannot be improved” is stated using the lower limit; this also establishes the claim for its upper-limit reading of average cost.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 446, §3 The infinite horizon undiscounted case, proof of Theorem 3, https://doi.org/10.1287/moor.12.3.441

import Definitions.Def_MDPComplexity_AverageCost_Model

namespace MDPComplexity.AverageCost

open Filter

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- §3, p. 446: no policy can improve on the least reachable cycle mean.
The lower limit makes the assertion valid even when a policy's averages oscillate. -/
theorem no_better_policy (M : DetMDP S) (s₀ : S) :
    ∀ (δ : M.Policy) (C₀ : M.Cycle),
      M.Reachable s₀ C₀.base →
      (∀ C : M.Cycle, M.Reachable s₀ C.base → C₀.mean ≤ C.mean) →
      C₀.mean ≤ liminf (M.average s₀ δ) atTop := by sorry

end MDPComplexity.AverageCost
