-- Prove2me | Theorems.Thm_MDPComplexity_AverageCost_min_plus_walks
-- name    : MDPComplexity.AverageCost.min_plus_walks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:58:16.7012+00:00
-- url     : https://prove2.me/theorems/42160d91-7d5e-4056-9a6e-fdd28b34614a
-- title:
--   Min-plus powers record cheapest decision walks
-- statement:
--   Let $A$ be the min-plus adjacency matrix of a finite deterministic process. For states $u,v$ and an integer $k\geq0$, the entry $(A^k)_{uv}$ is $+\infty$ exactly when there is no $k$-arc decision walk from $u$ to $v$. Whenever there is such a walk, the entry is the least of their total costs:
--
--   $$(A^k)_{uv}=\min\left\{\sum_{j=0}^{k-1}c(e_j):e_0,\ldots,e_{k-1}\text{ is a decision walk from }u\text{ to }v\right\}.$$
--
--   This identifies the matrix computation used for shortest closed walks. Parallel decisions are compared by cost; an absent arc has the extended value $+\infty$.
--
--   **Formalization Note** The zeroth power is the min-plus identity, so its diagonal entries are zero and other entries are infinite. A walk records each decision arc, not only its state sequence.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 446, §3 The infinite horizon undiscounted case, proof of Theorem 3, https://doi.org/10.1287/moor.12.3.441

import Definitions.Def_MDPComplexity_AverageCost_Model

namespace MDPComplexity.AverageCost

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- §3, p. 446: the kth min-plus power records exactly the cheapest k-arc
decision walk, and infinity records the absence of such a walk. -/
theorem min_plus_walks (M : DetMDP S) (k : ℕ) (u v : S) :
    (M.minPlusPow k u v = ⊤ ↔
      ¬ ∃ W : M.Walk k, W.start = u ∧ W.finish = v) ∧
    (∀ W : M.Walk k, W.start = u → W.finish = v →
      ∃ r : ℝ, M.minPlusPow k u v = (r : WithTop ℝ) ∧
        IsLeast {x : ℝ | ∃ W' : M.Walk k,
          W'.start = u ∧ W'.finish = v ∧ x = W'.cost} r) := by sorry

end MDPComplexity.AverageCost
