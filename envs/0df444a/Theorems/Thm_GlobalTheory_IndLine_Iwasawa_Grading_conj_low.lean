-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Grading_conj_low
-- name    : GlobalTheory.IndLine.Iwasawa.Grading.conj_low
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:52.135093+00:00
-- url     : https://prove2.me/theorems/a2901042-00ff-4688-bf79-7f4e0c00a7c7
-- title:
--   Grading: conj low
-- statement:
--   The Grading construction uses the conj low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L91-L97

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

theorem GlobalTheory.IndLine.Iwasawa.Grading.conj_low (Z : R) : θ * low p r q Z * θ = up p r q (θ * Z * θ) := by sorry
