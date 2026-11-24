-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integrable_density_of_bound_by_integral_on_compact
-- name    : GlobalTheory.T.exists_integrable_density_of_bound_by_integral_on_compact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:08.128338+00:00
-- url     : https://prove2.me/theorems/8921f44b-8be5-4af6-abaa-ae1cff7aa009
-- title:
--   T: exists integrable density of bound by integral on compact
-- statement:
--   The T construction uses the exists integrable density of bound by integral on compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegrableDensityOfBoundByIntegralCompactAStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegrableDensityOfBoundByIntegralCompactAStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegrableDensityOfBoundByIntegralCompactA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegrableDensityOfBoundByIntegralCompactAStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_integrable_density_of_bound_by_integral_on_compact : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by sorry
