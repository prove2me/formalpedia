-- Prove2me | Theorems.Thm_N25_Endgame_cusp_difference_killed25
-- name    : N25.Endgame.cusp_difference_killed25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:07.40035+00:00
-- url     : https://prove2.me/theorems/dd7bf60b-dab6-49bd-928b-b3f26d3ae83c
-- title:
--   Every selected cusp difference is annihilated by $71$
-- statement:
--   Let $p_i,p_j$ be any two of the five selected geometric cusps, and let $[p_i-p_j]$ be their degree-zero divisor class. Then
--
--   $$71[p_i-p_j]=0.$$
--
--   This places all selected cusp differences in the $71$-torsion cuspidal subgroup.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

set_option autoImplicit false
open AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.cusp_difference_killed25 (i j : Fin 5) :
    (71 : ℕ) • pointDiff (pG25 i) (pG25 j)
      ((pG25_degree i).trans (pG25_degree j).symm) = 0 := by sorry
