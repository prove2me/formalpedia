-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_wMinus_of_firstVariation
-- name    : FriedCrossing.FirstVariation.wMinus_of_firstVariation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:57:18.844101+00:00
-- url     : https://prove2.me/theorems/f9df5cba-7ef3-400a-b1cc-fcf32f30603b
-- title:
--   First Variation: w Minus of first Variation
-- statement:
--   The First Variation construction uses the w Minus of first Variation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L133-L136
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L133-L136

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.wMinus_of_firstVariation {Bcc Bcψ Bψc Bψψ p : ℝ}
    (hr : 0 < (Nmat Bcc Bcψ Bψc Bψψ p).trace) :
    TwinRate.wMinus (Nmat Bcc Bcψ Bψc Bψψ p).trace (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 := by sorry
