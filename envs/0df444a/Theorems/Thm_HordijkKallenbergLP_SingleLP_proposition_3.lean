-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_proposition_3
-- name    : HordijkKallenbergLP.SingleLP.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:05:56.822488+00:00
-- url     : https://prove2.me/theorems/e71bad0b-3019-40e6-baee-c97e478a0dd8
-- title:
--   Proposition 3 — at an extreme point, the states of E∖E_x are transient under P(f)
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, let $(x,y)$ be an optimal solution and an extreme point of the feasible set of the dual program (3)–(5), and let $f(i)=a_i$ follow the selection rule of Theorem 7. Then every state of $E\setminus E_x$ is transient in the Markov chain with transition probabilities
--   $$p_{ij}=p_{ia_ij},\qquad i,j\in E .$$
--
--   It is the third proposition of the proof of Theorem 7, and the only place where extremality is used.
--
--   **Formalization Note** A state $j$ is transient when it is not recurrent, recurrent meaning that every state accessible from $j$ leads back to $j$ (the published definition).
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 358, Proposition 3

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 3.** Let `(x, y)` be an extreme optimal solution of the dual program and
`f(i) = a_i` chosen by the rule of Theorem 7. The states of `E ∖ E_x` are transient in the Markov
chain with transition probabilities `p_{ij} = p_{i a_i j}`, `i, j ∈ E`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 358, Proposition 3.

**Formalization Note.** "Transient" is the negation of the published `IsRecurrent` (a state is
recurrent when every state accessible from it leads back to it). The paper's proof uses that
`(x, y)` is an extreme point ("Since (x, y) is an extreme point"); optimality is inherited from
the context of Theorem 7, though the proof of this proposition does not use it. -/
theorem proposition_3 (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hz : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    ∀ j ∉ Ex M z.1, ¬ IsRecurrent (transMatrix M f) j := by sorry

end HordijkKallenbergLP.SingleLP
