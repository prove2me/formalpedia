-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Model_nontrivial_transvection
-- name    : GlobalTheory.UTrans.Model.nontrivial_transvection
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:04.546276+00:00
-- url     : https://prove2.me/theorems/9015ac15-3f0a-45ec-9817-7d7a0f8a9f17
-- title:
--   Model: nontrivial transvection
-- statement:
--   The Model construction uses the nontrivial transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L79-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.UTrans.Model.nontrivial_transvection :
    !![1, Complex.I; 0, 1] ∈ TvGen (starRingEnd ℂ) !![0, 1; 1, 0] := by sorry
