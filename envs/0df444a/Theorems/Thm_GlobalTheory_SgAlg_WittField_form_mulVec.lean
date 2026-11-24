-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_form_mulVec
-- name    : GlobalTheory.SgAlg.WittField.form_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:39.708797+00:00
-- url     : https://prove2.me/theorems/1794a885-740a-4f13-a340-bb12cb414288
-- title:
--   Witt Field: form mul Vec
-- statement:
--   The Witt Field construction uses the form mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L48-L51

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

theorem GlobalTheory.SgAlg.WittField.form_mulVec (A B : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    form σ J (A *ᵥ v) (B *ᵥ w) = (fun i => σ (w i)) ⬝ᵥ ((cT σ B * J * A) *ᵥ v) := by sorry
