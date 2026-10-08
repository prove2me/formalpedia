-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_proposition_2
-- name    : HordijkKallenbergLP.SingleLP.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:05:36.694394+00:00
-- url     : https://prove2.me/theorems/d11fa81c-ba49-44cc-961c-b3af31697fb7
-- title:
--   Proposition 2 — E_x is closed under P(f)
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, let $(x,y)$ be an optimal solution of the dual program, and let $f(i)=a_i$ follow the selection rule of Theorem 7. Then $E_x$ is closed in the chain $P(f)$:
--   $$p_{ia_ij}=0,\qquad i\in E_x,\ j\notin E_x .$$
--
--   It is the second proposition of the proof of Theorem 7.
--
--   **Formalization Note** The paper states it inside the proof of Theorem 7, for an optimal $(x,y)$. Its proof uses only dual feasibility.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 358, Proposition 2

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 2.** For an optimal solution `(x, y)` of the dual program and `f(i) = a_i` chosen
by the rule of Theorem 7, `E_x` is closed, i.e. `p_{i a_i j} = 0` for `i ∈ E_x`, `j ∉ E_x`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 358, Proposition 2.

**Formalization Note.** The paper states it for the optimal `(x, y)` of Theorem 7; its proof uses
only constraint (3) and `x ≥ 0`. -/
theorem proposition_2 (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    ∀ i ∈ Ex M z.1, ∀ j ∉ Ex M z.1, M.trans i (f i) j = 0 := by sorry

end HordijkKallenbergLP.SingleLP
