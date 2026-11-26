-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_Bmat_mul_Nmat0
-- name    : FriedCrossing.FirstVariation.Bmat_mul_Nmat0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:48.429433+00:00
-- url     : https://prove2.me/theorems/befca9da-cce4-4c21-8f7d-750d8745eb26
-- title:
--   First Variation: Bmat mul Nmat0
-- statement:
--   The First Variation construction uses the Bmat mul Nmat0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L60-L64
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L60-L64

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.Bmat_mul_Nmat0 (Bcc Bcψ Bψc Bψψ p : K) :
    Bmat Bcc Bcψ Bψc Bψψ * Nmat0 Bcc Bcψ p = (Bcc * Bψψ - Bcψ * Bψc) • Pmat p := by sorry
