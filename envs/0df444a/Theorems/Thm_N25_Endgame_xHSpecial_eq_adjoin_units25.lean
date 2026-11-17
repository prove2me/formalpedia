-- Prove2me | Theorems.Thm_N25_Endgame_xHSpecial_eq_adjoin_units25
-- name    : N25.Endgame.xHSpecial_eq_adjoin_units25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:02.951236+00:00
-- url     : https://prove2.me/theorems/bfc22a13-a77f-4369-b0c5-28db0b9a4f68
-- title:
--   Two reduced modular-unit functions generate the special function field
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $R$ be a level-$25$ reduction datum at $p$, let $κ_R$ be its residue field, let $F_R$ be the associated special function field, and let $U_0,U_1∈F_R$ be the first two reduced modular units. Then
--
--   $$κ_R(U_0,U_0/U_1)=F_R.$$
--
--   This turns the coprime degrees four and seven into generation of the entire special function field.
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

theorem N25.Endgame.xHSpecial_eq_adjoin_units25 :
    IntermediateField.adjoin (κ R.A)
      ({U25C (κ R.A) 0, U25C (κ R.A) 0 / U25C (κ R.A) 1} : Set (FSpecial R.A)) = ⊤ := by sorry
