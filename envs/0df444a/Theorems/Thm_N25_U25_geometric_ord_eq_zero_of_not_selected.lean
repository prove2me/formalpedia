-- Prove2me | Theorems.Thm_N25_U25_geometric_ord_eq_zero_of_not_selected
-- name    : N25.U25_geometric_ord_eq_zero_of_not_selected
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:58.691613+00:00
-- url     : https://prove2.me/theorems/393e6c5d-4107-41f0-99f0-ce63948cdac1
-- title:
--   Each modular unit is supported only at five selected geometric cusps
-- statement:
--   Let $P_0^G,…,P_4^G$ be the selected geometric cusps. If $P≠P_j^G$ for every $j$, then $$ord_P(U_i^{geom})=0.$$ This reduces the support calculation to those five places.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
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
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

set_option autoImplicit false
open ModularCurve AlgebraicCurve N25.Endgame
open scoped MatrixGroups
open N25

theorem N25.U25_geometric_ord_eq_zero_of_not_selected (i : Fin 5) (P : GPlace)
    (hP : ∀ j : Fin 5, P ≠ pG25 j) : P.ord (emb25 (U25 i)) = 0 := by sorry
