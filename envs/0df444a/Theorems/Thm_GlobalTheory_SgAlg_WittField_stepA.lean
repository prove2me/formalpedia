-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_stepA
-- name    : GlobalTheory.SgAlg.WittField.stepA
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:13.595004+00:00
-- url     : https://prove2.me/theorems/acdcd371-8a62-4353-8a3a-38de999b017c
-- title:
--   Witt Field: step A
-- statement:
--   The Witt Field construction uses the step A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L113-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L113-L127

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

theorem GlobalTheory.SgAlg.WittField.stepA (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {a : ℕ} (y : Fin a → Fin n → E)
    (x x' : Fin n → E) (hy : ∀ i, form σ J (y i) x = form σ J (y i) x')
    (hxx : form σ J x x = form σ J x' x') (hc : form σ J x (x - x') ≠ 0) :
    ∃ g, IsUn σ J g ∧ (∀ i, g *ᵥ y i = y i) ∧ g *ᵥ x = x' := by sorry
