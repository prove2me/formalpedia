-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_of_form
-- name    : GlobalTheory.SgAlg.WittField.isUn_of_form
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:39.47399+00:00
-- url     : https://prove2.me/theorems/c8ff3d68-f63f-4353-b4e6-3ae4ab8147ad
-- title:
--   Witt Field: is Un of form
-- statement:
--   The Witt Field construction uses the is Un of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L66-L72

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

theorem GlobalTheory.SgAlg.WittField.isUn_of_form {g : Matrix (Fin n) (Fin n) E}
    (h : ∀ v w, form σ J (g *ᵥ v) (g *ᵥ w) = form σ J v w) : IsUn σ J g := by sorry
