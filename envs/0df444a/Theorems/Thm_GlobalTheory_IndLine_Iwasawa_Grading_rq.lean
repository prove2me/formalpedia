-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_rq
-- name    : GlobalTheory.IndLine.Iwasawa.Grading.rq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:16:29.052977+00:00
-- url     : https://prove2.me/theorems/9db68463-8103-4dd7-a8b9-6243aae3f567
-- title:
--   Grading: rq
-- statement:
--   The Grading construction uses the rq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L81-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L81-L81

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

theorem GlobalTheory.IndLine.Iwasawa.Grading.rq : r * q = 0 := by sorry
