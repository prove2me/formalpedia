-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Model_not_isU
-- name    : GlobalTheory.UTrans.Model.not_isU
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:58.078173+00:00
-- url     : https://prove2.me/theorems/781eb4e0-c26c-557d-8ff8-8681d1751af3
-- title:
--   Model: not is U
-- statement:
--   The Model construction uses the not is U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L103-L106

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

theorem GlobalTheory.UTrans.Model.not_isU : ¬ IsU (starRingEnd ℂ) !![0, 1; 1, 0] !![1, 1; 0, 1] := by sorry
