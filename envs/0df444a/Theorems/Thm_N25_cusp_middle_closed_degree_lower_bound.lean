-- Prove2me | Theorems.Thm_N25_cusp_middle_closed_degree_lower_bound
-- name    : N25.cusp_middle_closed_degree_lower_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:40.13976+00:00
-- url     : https://prove2.me/theorems/f3b71853-f435-4bd2-bf08-7acd5a0b7396
-- title:
--   A width-$5$ rational cusp has degree at least $4$
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$. There exists a rational cusp $Q$ such that the modular $j$-function has order $-5$ at $Q$ and
--
--   $$\deg Q\ge4.$$
--
--   This supplies the lower degree bound for the middle-width closed cusp. Formalization note: $\iota$ records the complex comparison used to construct the cusp.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false
open AlgebraicCurve ModularCurve
open scoped MatrixGroups
open N25
open N25.Endgame

theorem N25.cusp_middle_closed_degree_lower_bound (ι : Qbar →+* ℂ) :
    ∃ Q : QPlace, IsCusp j25 Q ∧ Q.ord j25 = -5 ∧ 4 ≤ Q.deg := by sorry
