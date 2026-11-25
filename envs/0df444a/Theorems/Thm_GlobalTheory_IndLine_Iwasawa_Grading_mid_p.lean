-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_mid_p
-- name    : GlobalTheory.IndLine.Iwasawa.Grading.mid_p
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:23.394331+00:00
-- url     : https://prove2.me/theorems/f604818d-e33d-5a55-8a1f-715e80ec53d9
-- title:
--   Grading: mid p
-- statement:
--   The Grading construction uses the mid p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L115-L117

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

theorem GlobalTheory.IndLine.Iwasawa.Grading.mid_p (Z : R) : mid p r q Z * p = p * mid p r q Z := by sorry
