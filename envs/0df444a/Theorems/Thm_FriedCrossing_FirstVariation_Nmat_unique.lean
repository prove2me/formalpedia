-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_Nmat_unique
-- name    : FriedCrossing.FirstVariation.Nmat_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:46:12.685662+00:00
-- url     : https://prove2.me/theorems/df310cbf-8c13-4289-a294-12b582ad3cb9
-- title:
--   First Variation: Nmat unique
-- statement:
--   N is the unique solution of B·N = P when B is invertible.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L71-L81
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L71-L81

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.Nmat_unique {Bcc Bcψ Bψc Bψψ p : K} (h : Bcc * Bψψ - Bcψ * Bψc ≠ 0)
    (N : Matrix (Fin 2) (Fin 2) K) (hN : Bmat Bcc Bcψ Bψc Bψψ * N = Pmat p) :
    N = Nmat Bcc Bcψ Bψc Bψψ p := by sorry
