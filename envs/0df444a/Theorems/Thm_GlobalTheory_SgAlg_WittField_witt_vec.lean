-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_witt_vec
-- name    : GlobalTheory.SgAlg.WittField.witt_vec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:13.643154+00:00
-- url     : https://prove2.me/theorems/08e817b4-fc70-41b8-9670-f887f433634e
-- title:
--   Witt Field: witt vec
-- statement:
--   The Witt Field construction uses the witt vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L185-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L185-L219

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

theorem GlobalTheory.SgAlg.WittField.witt_vec (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (hdet : IsUnit J.det) {δ : E}
    (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (h2 : (2 : E) ≠ 0) (a : ℕ) :
    ∀ (x x' ℓ ℓ' : Fin a → Fin n → E), (∀ i j, ℓ i ⬝ᵥ x j = if i = j then 1 else 0) →
      (∀ i j, ℓ' i ⬝ᵥ x' j = if i = j then 1 else 0) →
      (∀ i j, form σ J (x i) (x j) = form σ J (x' i) (x' j)) →
      ∃ g, IsUn σ J g ∧ ∀ j, g *ᵥ x j = x' j := by sorry
