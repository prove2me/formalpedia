-- Prove2me | Theorems.Thm_N25_U25_complex_ord_eq_zero_of_j_mem
-- name    : N25.U25_complex_ord_eq_zero_of_j_mem
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:30.326891+00:00
-- url     : https://prove2.me/theorems/578c5000-0358-43e3-a746-a6feef31ba22
-- title:
--   Regularity of $j$ forces modular-unit order zero
-- statement:
--   Let $x$ have the $i$th complex unit series, let $P$ be a place, and let $j$ have the classical $j$-series. If $j$ lies in the valuation ring of $P$, then $$ord_P(x)=0.$$ This confines unit divisors to cusps.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem

set_option autoImplicit false
open UpperHalfPlane ModularCurve AlgebraicCurve
open N25

theorem N25.U25_complex_ord_eq_zero_of_j_mem (i : Fin 5)
    (x : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hx : (x : LaurentSeries ℂ) = unitSeries25 ℂ i)
    (P : Place ℂ (laurentBaseChange ℂ (xHFunctionField 25 N25.H25)))
    (j : laurentBaseChange ℂ (xHFunctionField 25 N25.H25))
    (hj : (j : LaurentSeries ℂ) = jqModC ℂ) (hP : j ∈ P.toValuationSubring) :
    P.ord x = 0 := by sorry
