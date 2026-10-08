-- Prove2me | Theorems.Thm_KallenbergLP_Games_value_smallest_superharmonic
-- name    : KallenbergLP.Games.value_smallest_superharmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:56:00.881986+00:00
-- url     : https://prove2.me/theorems/180a9b0c-3665-408f-bafb-87bdaf4101e1
-- title:
--   Theorem 6.2.2 — val(TMG) is the smallest TMG-superharmonic vector
-- statement:
--   Let $(E,A,B,p,r)$ be a two-person zero-sum stochastic game satisfying Assumption 6.2.1. There is a value $y = \mathrm{val(TMG)} = v(R_1^*,R_2^*)$ for a pair $(R_1^*,R_2^*)$ of optimal policies. This $y$ is TMG-superharmonic: there is a stationary policy $\rho^\infty$ of player II with
--   $$y_i \ge r_{ia}(\rho) + \sum_j p_{iaj}(\rho)\,y_j, \qquad a \in A(i),\ i \in E,$$
--   and $y \le y'$ componentwise for every TMG-superharmonic vector $y'$.
--
--   This characterization turns the value into the optimal solution of a nonlinear program, and, under Assumption 6.2.2, into the linear program (6.2.1).
--
--   **Formalization Note** Existence of the value is part of this statement and follows from Theorem 6.2.1. Assumption 6.2.2 is not assumed.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 193, Theorem 6.2.2 (under Assumption 6.2.1, p. 192; Definition 6.2.1, p. 193)

import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.2 (p. 193): under Assumption 6.2.1, `val(TMG)` is the smallest TMG-superharmonic
vector. -/
theorem value_smallest_superharmonic {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) :
    ∃ y : Fin N → ℝ, IsValueOfGame G y ∧
      IsLeast {y' : Fin N → ℝ | TMGSuperharmonic G y'} y := by sorry

end KallenbergLP.Games
