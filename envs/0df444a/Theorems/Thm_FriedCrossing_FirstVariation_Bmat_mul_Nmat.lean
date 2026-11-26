-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_Bmat_mul_Nmat
-- name    : FriedCrossing.FirstVariation.Bmat_mul_Nmat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:46:02.27437+00:00
-- url     : https://prove2.me/theorems/9b409ca5-171d-40c3-92d4-dc1e78c59b9b
-- title:
--   First Variation: Bmat mul Nmat
-- statement:
--   The First Variation construction uses the Bmat mul Nmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L66-L68
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L66-L68

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.Bmat_mul_Nmat {Bcc Bcψ Bψc Bψψ p : K} (h : Bcc * Bψψ - Bcψ * Bψc ≠ 0) :
    Bmat Bcc Bcψ Bψc Bψψ * Nmat Bcc Bcψ Bψc Bψψ p = Pmat p := by sorry
