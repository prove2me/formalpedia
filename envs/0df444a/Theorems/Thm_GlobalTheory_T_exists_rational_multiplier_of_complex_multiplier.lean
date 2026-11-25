-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_rational_multiplier_of_complex_multiplier
-- name    : GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:51.276455+00:00
-- url     : https://prove2.me/theorems/72014aa4-91ac-49bc-8e39-14c5dc7982f0
-- title:
--   T: exists rational multiplier of complex multiplier
-- statement:
--   The T construction uses the exists rational multiplier of complex multiplier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalMultiplierOfComplexMultiplierStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalMultiplierOfComplexMultiplierStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalMultiplierOfComplexMultiplier
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalMultiplierOfComplexMultiplierStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by sorry
