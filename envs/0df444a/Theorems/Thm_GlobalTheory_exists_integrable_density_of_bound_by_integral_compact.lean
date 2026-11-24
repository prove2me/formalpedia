-- Prove2me | Theorems.Thm_GlobalTheory_exists_integrable_density_of_bound_by_integral_compact
-- name    : GlobalTheory.exists_integrable_density_of_bound_by_integral_compact
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:26.319626+00:00
-- url     : https://prove2.me/theorems/187653c2-152d-4910-a7bd-b2afc01f026d
-- title:
--   Global Theory: exists integrable density of bound by integral compact
-- statement:
--   The Global Theory construction uses the exists integrable density of bound by integral compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegrableDensityOfBoundByIntegralCompactA.lean#L6-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegrableDensityOfBoundByIntegralCompactA.lean#L6-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegrableDensityOfBoundByIntegralCompactA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.exists_integrable_density_of_bound_by_integral_compact : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by sorry
