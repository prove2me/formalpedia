-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_3_4
-- name    : KallenbergLP.AverageLP.theorem_4_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:34:21.442246+00:00
-- url     : https://prove2.me/theorems/e9c8c3e5-d4a5-49b8-a50f-2bba2f86b75d
-- title:
--   Theorem 4.3.4 — the representative of a pure stationary policy is an extreme feasible solution
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$ and let $f^\infty$ be any pure and stationary policy. Then the representative $(x(f),y(f))$, defined by (4.3.2) for the stationary policy with $\pi_{ia}=1$ if $a=f(i)$ and $0$ otherwise, is an extreme point of the set of feasible solutions of the linear program (4.2.11).
--
--   Together with Theorems 4.2.4 and 4.3.3 this shows that every pure stationary average optimal policy is obtained from some extreme optimal solution (Remark 4.2.5).
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 115, Theorem 4.3.4

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.3.4.** Let `f^∞` be any pure and stationary policy. Then the corresponding vector
`(x(f), y(f))`, defined by (4.3.2), is an extreme feasible solution of (4.2.11).

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 115, Theorem 4.3.4. -/
theorem theorem_4_3_4 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    (xRep M β (pureStat M f hf), yRep M β (pureStat M f hf)) ∈
      Set.extremePoints ℝ (dualFeasible M β) := by sorry

end KallenbergLP.AverageLP
