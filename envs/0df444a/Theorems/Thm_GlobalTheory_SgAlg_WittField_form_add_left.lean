-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_form_add_left
-- name    : GlobalTheory.SgAlg.WittField.form_add_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:41.188801+00:00
-- url     : https://prove2.me/theorems/69bdcf4a-c658-4513-a2bb-51749656d89b
-- title:
--   Witt Field: form add left
-- statement:
--   The Witt Field construction uses the form add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.SgAlg.WittField.form_add_left (v v' w : Fin n → E) : form σ J (v + v') w = form σ J v w + form σ J v' w := by sorry
