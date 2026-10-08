-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_proposition_4_3_3
-- name    : KallenbergLP.AverageLP.proposition_4_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:34:15.339735+00:00
-- url     : https://prove2.me/theorems/55670679-8f50-49b7-9e07-8b6c1cc368d9
-- title:
--   Proposition 4.3.3 — $E_x$ is exactly the set of recurrent states of $P(\pi(x,y))$
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$. For any feasible solution $(x,y)$ of the linear program (4.2.11), the set $E_x=\{i\mid\sum_ax_{ia}>0\}$ is the set of recurrent states of the Markov chain with transition matrix $P(\pi(x,y))$, where $\pi(x,y)$ is the stationary policy (4.3.1).
--
--   A state $i$ is recurrent if every state accessible from $i$ leads back to $i$.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 114, Proposition 4.3.3 (proof of Theorem 4.3.3)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 4.3.3** (proof of Theorem 4.3.3, part 2). For any feasible solution `(x, y) = z`
of the linear program (4.2.11), `E_x` is the set of recurrent states in the Markov chain induced
by `P(π(x, y))`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 114, Proposition 4.3.3.

**Formalization Note.** Recurrence is the published `IsRecurrent` (every state accessible from `i`
leads back to `i`). -/
theorem proposition_4_3_3 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hz : z ∈ dualFeasible M β) :
    ∀ i : S, IsRecurrent (weightMatrix M (dualPolicyWeight M z.1 z.2)) i ↔ i ∈ Ex M z.1 := by sorry

end KallenbergLP.AverageLP
