-- Prove2me | Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_special_zero_LSpace_finiteDimensional25
-- name    : N25.Endgame.SpecialUnitPoleDegrees.special_zero_LSpace_finiteDimensional25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:44.14695+00:00
-- url     : https://prove2.me/theorems/235aab77-482a-4274-a9da-3b8cdbe9cdf5
-- title:
--   The zero-divisor Riemann–Roch space is finite-dimensional
-- statement:
--   Let $p$ be prime, let $R$ be a level-$25$ reduction datum at $p$, let $κ=κ(R.A)$ be its residue field, let $F=F_{special}(R.A)$ be the special function field, and let $L_F(0)$ be the Riemann–Roch space of functions without poles. Then
--
--   $$dim_κ L_F(0)<∞.$$
--
--   This provides the constant-space finiteness required by the pole-degree formula.
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
omit hp

theorem N25.Endgame.SpecialUnitPoleDegrees.special_zero_LSpace_finiteDimensional25 :
    FiniteDimensional (κ R.A) (LSpace (0 : Divisor (κ R.A) (FSpecial R.A))) := by sorry
