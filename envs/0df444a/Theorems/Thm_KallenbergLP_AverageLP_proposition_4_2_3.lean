-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_proposition_4_2_3
-- name    : KallenbergLP.AverageLP.proposition_4_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:46.233583+00:00
-- url     : https://prove2.me/theorems/e0c787c8-e69f-41eb-97ad-0b5279ab8dbd
-- title:
--   Proposition 4.2.3 — the states outside $E_{x^*}$ are transient under $P(f_*)$
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, let $(x^*,y^*)$ be an optimal solution of the dual program (4.2.11) that is an extreme point of its feasible set, and let $f_*$ be chosen by the rule of Theorem 4.2.4. Then every state of $E\setminus E_{x^*}$ is transient in the Markov chain with transition matrix $P(f_*)=(p_{if_*(i)j})$.
--
--   Here a state $j$ is recurrent if every state accessible from $j$ leads back to $j$, and transient otherwise. This is where the extreme-point hypothesis enters the proof of Theorem 4.2.4.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 105, Proposition 4.2.3 (proof of Theorem 4.2.4)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 4.2.3** (proof of Theorem 4.2.4). With `(x*, y*) = z` is an optimal solution of (4.2.11) that is an extreme point of its feasible set,
with `β_j > 0`, `Σ_j β_j = 1`, and `f_*` = `f` is chosen by the rule of Theorem 4.2.4 (the context
of the proof of Theorem 4.2.4, pp. 103–105). Then the states of
`E ∖ E_{x*}` are transient in the Markov chain induced by `P(f_*)`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 105, Proposition 4.2.3.

**Formalization Note.** "Transient" is the negation of the published `IsRecurrent` (every state
accessible from `j` leads back to `j`), the classical notion for a finite chain. -/
theorem proposition_4_2_3 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    ∀ j ∉ Ex M z.1, ¬ IsRecurrent (Pf M f) j := by sorry

end KallenbergLP.AverageLP
