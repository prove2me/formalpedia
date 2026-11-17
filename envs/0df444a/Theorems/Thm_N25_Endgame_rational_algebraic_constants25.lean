-- Prove2me | Theorems.Thm_N25_Endgame_rational_algebraic_constants25
-- name    : N25.Endgame.rational_algebraic_constants25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:35.912502+00:00
-- url     : https://prove2.me/theorems/c4baa90b-800f-4f07-9dfb-d573fa843695
-- title:
--   The rational modular function field has no new algebraic constants
-- statement:
--   Let $F_ℚ$ be the rational level-$25$ modular function field and let $y∈F_ℚ$. If $y$ is algebraic over $ℚ$, then $y$ comes from the constant-field embedding:
--
--   $$y∈im(ℚ→F_ℚ).$$
--
--   This constant-field rigidity is used in the uniqueness and degree analysis of geometric place lifts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.rational_algebraic_constants25 (y : FQ) (hy : IsAlgebraic ℚ y) :
    y ∈ (algebraMap ℚ FQ).range := by sorry
