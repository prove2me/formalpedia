-- Prove2me | Theorems.Thm_N25_unitOrders25_principal_combination
-- name    : N25.unitOrders25_principal_combination
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:10.980689+00:00
-- url     : https://prove2.me/theorems/cfe29052-a838-45d6-8447-7b360ee3f157
-- title:
--   Every integer combination of the five unit divisors is principal
-- statement:
--   Let $P_0^G,…,P_4^G$ be the selected geometric cusp places, let $m_{rk}$ be the unit-order table, and define $D_r=\sum_k m_{rk}[P_k^G]$. For any integers $c_0,…,c_4$, $$\sum_{r=0}^{4}c_rD_r\text{ is a principal divisor}.$$ This packages arbitrary products of the five modular units into divisor relations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
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
open AlgebraicCurve N25.Endgame
open N25

theorem N25.unitOrders25_principal_combination (c : Fin 5 → ℤ) :
    Divisor.IsPrincipal (∑ r : Fin 5, c r •
      ∑ k : Fin 5, Finsupp.single (pG25 k) (unitOrders25 r k)) := by sorry
