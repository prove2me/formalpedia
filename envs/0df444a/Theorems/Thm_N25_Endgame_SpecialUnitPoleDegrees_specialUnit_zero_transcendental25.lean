-- Prove2me | Theorems.Thm_N25_Endgame_SpecialUnitPoleDegrees_specialUnit_zero_transcendental25
-- name    : N25.Endgame.SpecialUnitPoleDegrees.specialUnit_zero_transcendental25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:14.739755+00:00
-- url     : https://prove2.me/theorems/2cf01fcc-434a-42bd-8585-2e67f0b0755b
-- title:
--   The first reduced modular unit is transcendental
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $R$ be a level-$25$ reduction datum at $p$, let $κ_R$ be its residue field, and let $F_R$ be the corresponding special function field. The first reduced modular unit $U_0∈F_R$ is transcendental over $κ_R$:
--
--   $$U_0\notin\overline{κ_R}^{\,F_R}.$$
--
--   This ensures that adjoining $U_0$ defines a genuine finite map of curves rather than a constant extension.
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

theorem N25.Endgame.SpecialUnitPoleDegrees.specialUnit_zero_transcendental25 :
    Transcendental (κ R.A) (U25C (κ R.A) 0) := by sorry
