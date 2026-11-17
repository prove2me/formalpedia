-- Prove2me | Theorems.Thm_N25_Endgame_specialUnit_ratio_finrank25
-- name    : N25.Endgame.specialUnit_ratio_finrank25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:10.339704+00:00
-- url     : https://prove2.me/theorems/77799a41-0a50-4b58-8d18-7c5937786c37
-- title:
--   The reduced unit ratio has pole degree seven
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $R$ be a level-$25$ reduction datum at $p$, let $κ_R$ be its residue field, let $F_R$ be the special function field, and let $U_0,U_1∈F_R$ be the first two reduced modular units. Then
--
--   $$[F_R:κ_R(U_0/U_1)]=7.$$
--
--   This supplies the second coprime simple-subfield degree in the modular-unit generation argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType

set_option autoImplicit false
open AlgebraicCurve N25.Endgame
open N25
open N25.Endgame
open N25
variable {p : ℕ} [Fact p.Prime] (hp : p = 2 ∨ p = 3) (R : RedDatum25 p)
include hp

theorem N25.Endgame.specialUnit_ratio_finrank25 :
    Module.finrank
      (IntermediateField.adjoin (κ R.A)
        ({U25C (κ R.A) 0 / U25C (κ R.A) 1} : Set (FSpecial R.A)))
      (FSpecial R.A) = 7 := by sorry
