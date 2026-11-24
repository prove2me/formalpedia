-- Prove2me | Theorems.Thm_GlobalTheory_exists_rational_multiplier_of_complex
-- name    : GlobalTheory.exists_rational_multiplier_of_complex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:12.010827+00:00
-- url     : https://prove2.me/theorems/d425ad96-0260-4564-9cbc-feda481b0636
-- title:
--   Global Theory: exists rational multiplier of complex
-- statement:
--   The Global Theory construction uses the exists rational multiplier of complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalMultiplierOfComplexMultiplier.lean#L60-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalMultiplierOfComplexMultiplier.lean#L60-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalMultiplierOfComplexMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module

theorem GlobalTheory.exists_rational_multiplier_of_complex :
    ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by sorry
