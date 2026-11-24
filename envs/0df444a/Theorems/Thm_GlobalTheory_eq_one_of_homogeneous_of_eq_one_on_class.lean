-- Prove2me | Theorems.Thm_GlobalTheory_eq_one_of_homogeneous_of_eq_one_on_class
-- name    : GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:18:03.382045+00:00
-- url     : https://prove2.me/theorems/55896e0c-de08-46c1-a9f7-fbd52e38e18c
-- title:
--   Global Theory: eq one of homogeneous of eq one on class
-- statement:
--   The Global Theory construction uses the eq one of homogeneous of eq one on class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RayInvariantContinuousEqOne.lean#L30-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RayInvariantContinuousEqOne.lean#L30-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RayInvariantContinuousEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (φ : mixedSpace K → ℂ), m ≠ ⊥ → ContinuousOn φ {x | mixedEmbedding.norm x ≠ 0} → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → φ (mixedEmbedding K β) = 1) → ∀ x, mixedEmbedding.norm x ≠ 0 → φ x = 1 := by sorry
