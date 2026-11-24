-- Prove2me | Theorems.Thm_GlobalTheory_QFam_isFam_algebra
-- name    : GlobalTheory.QFam.isFam_algebra
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:12:13.713544+00:00
-- url     : https://prove2.me/theorems/4c16063a-3a64-449b-bc51-a568fb2df9a8
-- title:
--   QFam: is Fam algebra
-- statement:
--   The QFam construction uses the is Fam algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyAlgebraClosure.lean#L76-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyAlgebraClosure.lean#L76-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ModularForm
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}

theorem GlobalTheory.QFam.isFam_algebra : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι),
    (∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c) ∧
    (∀ w f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w g →
      (_root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ + g i τ) ∧
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ - g i τ) ∧
    (∀ w (c : ℂ) f, _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ) ∧
    (∀ w w' f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w' g →
      _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ) ∧
    (∀ w f (k : ℕ), _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k) ∧
    (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) →
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act (w k) (f k)) →
        _root_.GlobalTheory.QFam.IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f,
      (∀ k γ, φ (act' k γ) = act (φ k) γ) → _root_.GlobalTheory.QFam.IsFam act w f →
        _root_.GlobalTheory.QFam.IsFam act' w fun k => f (φ k)) := by sorry
