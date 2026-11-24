-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_step
-- name    : GlobalTheory.SgAlg.WittField.step
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:27.853713+00:00
-- url     : https://prove2.me/theorems/2ae5cc40-4e16-4b2f-831a-4ca3d83e61dc
-- title:
--   Witt Field: step
-- statement:
--   The Witt Field construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L129-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L129-L176

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

theorem GlobalTheory.SgAlg.WittField.step (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (h2 : (2 : E) ≠ 0) {a : ℕ} (y : Fin a → Fin n → E)
    (x x' : Fin n → E) (hy : ∀ i, form σ J (y i) x = form σ J (y i) x')
    (hxx : form σ J x x = form σ J x' x') (u₁ u₂ : Fin n → E)
    (hu₁ : ∀ i, form σ J (y i) u₁ = 0) (hxu₁ : form σ J x u₁ = 1)
    (hu₂ : ∀ i, form σ J (y i) u₂ = 0) (hxu₂ : form σ J x' u₂ = 1) :
    ∃ g, IsUn σ J g ∧ (∀ i, g *ᵥ y i = y i) ∧ g *ᵥ x = x' := by sorry
