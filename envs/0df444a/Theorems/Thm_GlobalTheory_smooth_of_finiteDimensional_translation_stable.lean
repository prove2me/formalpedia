-- Prove2me | Theorems.Thm_GlobalTheory_smooth_of_finiteDimensional_translation_stable
-- name    : GlobalTheory.smooth_of_finiteDimensional_translation_stable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:42.656258+00:00
-- url     : https://prove2.me/theorems/75db8b4a-86be-480d-a193-deab78143841
-- title:
--   Global Theory: smooth of finite Dimensional translation stable
-- statement:
--   The Global Theory construction uses the smooth of finite Dimensional translation stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothOfFiniteDimensionalTranslationStable.lean#L20-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothOfFiniteDimensionalTranslationStable.lean#L20-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContDiffOfContinuousOneParameterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothOfFiniteDimensionalTranslationStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.smooth_of_finiteDimensional_translation_stable :
    ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by sorry
