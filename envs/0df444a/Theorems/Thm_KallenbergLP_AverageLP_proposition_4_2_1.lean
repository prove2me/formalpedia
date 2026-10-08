-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_proposition_4_2_1
-- name    : KallenbergLP.AverageLP.proposition_4_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:14.77254+00:00
-- url     : https://prove2.me/theorems/e24dfcbe-33c5-47c8-8089-c89a32515922
-- title:
--   Proposition 4.2.1 — complementary slackness along the policy read off an extreme optimal dual solution
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$, let $(x^*,y^*)$ be an optimal solution of the dual program (4.2.11) that is an extreme point of its feasible set, and let $f_*$ be any decision rule with $x^*_{if_*(i)}>0$ for $i\in E_{x^*}=\{i\mid\sum_ax^*_{ia}>0\}$ and $y^*_{if_*(i)}>0$ for $i\notin E_{x^*}$. Let $(\phi,u)$ be an optimal solution of the primal program (4.2.10). Then
--   $$\sum_j(\delta_{ij}-p_{if_*(i)j})\phi_j=0\quad(i\in E),\qquad \phi_i+\sum_j(\delta_{ij}-p_{if_*(i)j})u_j=r_i(f_*)\quad(i\in E_{x^*}).$$
--
--   This is the first of the three propositions from which Theorem 4.2.4 is assembled.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 103, Proposition 4.2.1 (proof of Theorem 4.2.4)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 4.2.1** (proof of Theorem 4.2.4). With `(x*, y*) = z` is an optimal solution of (4.2.11) that is an extreme point of its feasible set,
with `β_j > 0`, `Σ_j β_j = 1`, and `f_*` = `f` is chosen by the rule of Theorem 4.2.4 (the context
of the proof of Theorem 4.2.4, pp. 103–105). Let `(φ, u)` be an optimal
solution of the primal program (4.2.10). Then
`Σ_j (δ_ij − p_{i f_*(i) j}) φ_j = 0` for `i ∈ E`, and
`φ_i + Σ_j (δ_ij − p_{i f_*(i) j}) u_j = r_i(f_*)` for `i ∈ E_{x*}`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 103, Proposition 4.2.1. -/
theorem proposition_4_2_1 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf)
    (φ u : S → ℝ) (hφu : IsPrimalOptimal M β φ u) :
    (∀ i, ∑ j, ((if i = j then (1 : ℝ) else 0) - M.trans i (f i) j) * φ j = 0) ∧
    (∀ i ∈ Ex M z.1,
      φ i + ∑ j, ((if i = j then (1 : ℝ) else 0) - M.trans i (f i) j) * u j = rf M f i) := by sorry

end KallenbergLP.AverageLP
