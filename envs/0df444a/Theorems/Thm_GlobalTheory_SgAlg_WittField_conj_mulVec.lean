-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_conj_mulVec
-- name    : GlobalTheory.SgAlg.WittField.conj_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:13.094505+00:00
-- url     : https://prove2.me/theorems/fdfcc4f3-07c3-49dd-b0db-1e34326818da
-- title:
--   Witt Field: conj mul Vec
-- statement:
--   The Witt Field construction uses the conj mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L43-L46

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

theorem GlobalTheory.SgAlg.WittField.conj_mulVec (B : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    (fun i => σ ((B *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* cT σ B := by sorry
