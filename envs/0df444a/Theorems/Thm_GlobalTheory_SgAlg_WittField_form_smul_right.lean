-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_form_smul_right
-- name    : GlobalTheory.SgAlg.WittField.form_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:21.398255+00:00
-- url     : https://prove2.me/theorems/59f767f0-bcf9-4260-8414-b6c19e833342
-- title:
--   Witt Field: form smul right
-- statement:
--   The Witt Field construction uses the form smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L23-L25

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

theorem GlobalTheory.SgAlg.WittField.form_smul_right (c : E) (v w : Fin n → E) : form σ J v (c • w) = σ c * form σ J v w := by sorry
