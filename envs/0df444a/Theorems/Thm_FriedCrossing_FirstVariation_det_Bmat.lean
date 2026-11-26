-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_det_Bmat
-- name    : FriedCrossing.FirstVariation.det_Bmat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:45:46.353379+00:00
-- url     : https://prove2.me/theorems/c226efab-b647-4868-a7ee-a9f8c0602734
-- title:
--   First Variation: det Bmat
-- statement:
--   The First Variation construction uses the det Bmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L56-L58
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L56-L58

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.det_Bmat (Bcc Bcψ Bψc Bψψ : K) :
    (Bmat Bcc Bcψ Bψc Bψψ).det = Bcc * Bψψ - Bcψ * Bψc := by sorry
