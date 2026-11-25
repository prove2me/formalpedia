-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_comm_cpt
-- name    : GlobalTheory.IndLine.Iwasawa.Grading.comm_cpt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:29.085941+00:00
-- url     : https://prove2.me/theorems/2bce5db5-c52b-4906-80d3-91849e2ec04a
-- title:
--   Grading: comm cpt
-- statement:
--   The Grading construction uses the comm cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L105-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {R : Type} [Ring R]
open GlobalTheory.IndLine.Iwasawa.Grading
variable {p r q θ : R} (h : Grading p r q θ)
include h

theorem GlobalTheory.IndLine.Iwasawa.Grading.comm_cpt (Z : R) : Commute (low p r q Z + θ * low p r q Z * θ) θ := by sorry
