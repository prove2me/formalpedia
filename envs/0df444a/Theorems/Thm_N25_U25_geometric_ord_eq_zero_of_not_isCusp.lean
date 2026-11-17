-- Prove2me | Theorems.Thm_N25_U25_geometric_ord_eq_zero_of_not_isCusp
-- name    : N25.U25_geometric_ord_eq_zero_of_not_isCusp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:16.131742+00:00
-- url     : https://prove2.me/theorems/48ad0bf8-ad43-409c-af88-2e41ca7663f2
-- title:
--   Each modular unit has order zero at every geometric noncusp
-- statement:
--   Let $P$ be a geometric place and let $U_i^{geom}$ be the geometric image of the $i$th modular unit. If $P$ is not a cusp for the embedded $j$-map, then $$ord_P(U_i^{geom})=0.$$ Thus the geometric divisor is cuspidal.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

set_option autoImplicit false
open ModularCurve AlgebraicCurve N25.Endgame
open N25

theorem N25.U25_geometric_ord_eq_zero_of_not_isCusp (i : Fin 5) (P : GPlace)
    (hP : ¬ ModularCurve.IsCusp (emb25 j25) P) :
    P.ord (emb25 (U25 i)) = 0 := by sorry
