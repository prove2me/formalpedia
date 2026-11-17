-- Prove2me | Theorems.Thm_N25_Endgame_rational_reduction_fixed
-- name    : N25.Endgame.rational_reduction_fixed
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:53.302782+00:00
-- url     : https://prove2.me/theorems/6ba4322d-f640-4fae-b9a6-26d5d97d7091
-- title:
--   A rational geometric place reduces to a Frobenius-fixed place modulo $2$
-- statement:
--   Let $D_2$ be a level-$25$ reduction datum at $2$, let $P$ be a degree-one geometric place fixed by arithmetic Galois, let $red_{D_2}(P)$ be its reduction, and let $Fr_{D_2}$ be Frobenius on special-fiber places. Then
--
--   $$Fr_{D_2}(red_{D_2}(P))=red_{D_2}(P).$$
--
--   This sends rational geometric places into the five-element Frobenius fixed-point set.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_PointDifference
import Definitions.Def_N25_CuspReduction
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_UnitSeries
import Definitions.Def_N25_Endgame
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_ModularCurve_genusFF_gammaH_residueField_eq_of_not_dvd
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.rational_reduction_fixed
    (D₂ : N25.Endgame.RedDatum25 2)
    (P : N25.Endgame.GPlace)
    (hP : N25.Endgame.IsRationalGeomPlace P) :
    N25.Endgame.frobPlace25 D₂ (N25.Endgame.redPlace25 D₂ P) =
      N25.Endgame.redPlace25 D₂ P := by sorry
