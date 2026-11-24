-- Prove2me | Theorems.Thm_GlobalTheory_T_deriv_mem_and_contDiff_of_translation_stable
-- name    : GlobalTheory.T.deriv_mem_and_contDiff_of_translation_stable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:11.798103+00:00
-- url     : https://prove2.me/theorems/7a9ab4c1-ee68-4092-94e0-e2f4c75508a6
-- title:
--   T: deriv mem and cont Diff of translation stable
-- statement:
--   The T construction uses the deriv mem and cont Diff of translation stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothOfFiniteDimensionalTranslationStableStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothOfFiniteDimensionalTranslationStableStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothOfFiniteDimensionalTranslationStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothOfFiniteDimensionalTranslationStableStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.deriv_mem_and_contDiff_of_translation_stable : ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by sorry
