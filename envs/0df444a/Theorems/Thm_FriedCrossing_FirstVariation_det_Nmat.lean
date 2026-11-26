-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_det_Nmat
-- name    : FriedCrossing.FirstVariation.det_Nmat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:39:27.214673+00:00
-- url     : https://prove2.me/theorems/12816c6d-a13f-5326-92eb-d4d20b4b65af
-- title:
--   First Variation: det Nmat
-- statement:
--   The First Variation construction uses the det Nmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L90-L91
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L90-L91

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.det_Nmat (Bcc Bcψ Bψc Bψψ p : K) : (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 := by sorry
