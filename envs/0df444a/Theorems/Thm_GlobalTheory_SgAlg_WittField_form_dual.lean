-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_form_dual
-- name    : GlobalTheory.SgAlg.WittField.form_dual
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:32.897799+00:00
-- url     : https://prove2.me/theorems/3427ff8c-bd0e-4441-9ef7-6933c1ad09d3
-- title:
--   Witt Field: form dual
-- statement:
--   The Witt Field construction uses the form dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L178-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L178-L183

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

theorem GlobalTheory.SgAlg.WittField.form_dual (hσ : ∀ x, σ (σ x) = x) (hdet : IsUnit J.det) (m v : Fin n → E) :
    form σ J v (fun k => σ ((m ᵥ* J⁻¹) k)) = m ⬝ᵥ v := by sorry
