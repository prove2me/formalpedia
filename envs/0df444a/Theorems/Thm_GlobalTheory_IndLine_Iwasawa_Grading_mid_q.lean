-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_mid_q
-- name    : GlobalTheory.IndLine.Iwasawa.Grading.mid_q
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:46.686617+00:00
-- url     : https://prove2.me/theorems/21bc5726-1727-47e9-92b9-7edc1a066ec1
-- title:
--   Grading: mid q
-- statement:
--   The Grading construction uses the mid q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L119-L121

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

theorem GlobalTheory.IndLine.Iwasawa.Grading.mid_q (Z : R) : mid p r q Z * q = q * mid p r q Z := by sorry
