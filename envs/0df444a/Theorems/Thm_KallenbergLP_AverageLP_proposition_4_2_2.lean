-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_proposition_4_2_2
-- name    : KallenbergLP.AverageLP.proposition_4_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:24.312588+00:00
-- url     : https://prove2.me/theorems/8695ca77-43d0-4288-91f7-137df52af257
-- title:
--   Proposition 4.2.2 — $E_{x^*}$ is closed under $P(f_*)$
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, let $(x^*,y^*)$ be an optimal solution of the dual program (4.2.11) that is an extreme point of its feasible set, and let $f_*$ be chosen by the rule of Theorem 4.2.4 ($x^*_{if_*(i)}>0$ on $E_{x^*}$, $y^*_{if_*(i)}>0$ off it). Then $E_{x^*}$ is closed under $P(f_*)$:
--   $$p_{if_*(i)j}=0\qquad\text{for all }i\in E_{x^*},\ j\notin E_{x^*}.$$
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 104, Proposition 4.2.2 (proof of Theorem 4.2.4)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 4.2.2** (proof of Theorem 4.2.4). With `(x*, y*) = z` is an optimal solution of (4.2.11) that is an extreme point of its feasible set,
with `β_j > 0`, `Σ_j β_j = 1`, and `f_*` = `f` is chosen by the rule of Theorem 4.2.4 (the context
of the proof of Theorem 4.2.4, pp. 103–105). Then `E_{x*}` is closed under
`P(f_*)`, i.e. `p_{i f_*(i) j} = 0` for `i ∈ E_{x*}`, `j ∉ E_{x*}`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 104, Proposition 4.2.2. -/
theorem proposition_4_2_2 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    IsClosedUnder (Pf M f) (Ex M z.1) := by sorry

end KallenbergLP.AverageLP
