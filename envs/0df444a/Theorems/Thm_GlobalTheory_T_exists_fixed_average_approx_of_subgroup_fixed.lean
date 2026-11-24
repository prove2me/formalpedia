-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_fixed_average_approx_of_subgroup_fixed
-- name    : GlobalTheory.T.exists_fixed_average_approx_of_subgroup_fixed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:40.062077+00:00
-- url     : https://prove2.me/theorems/1b0170dc-786e-4284-ac27-54c82546c59c
-- title:
--   T: exists fixed average approx of subgroup fixed
-- statement:
--   The T construction uses the exists fixed average approx of subgroup fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFixedAverageApproxOfSubgroupFixedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFixedAverageApproxOfSubgroupFixedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFixedAverageApproxOfSubgroupFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFixedAverageApproxOfSubgroupFixedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_fixed_average_approx_of_subgroup_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (H U : Subgroup G), IsOpen (U : Set G) → (∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H) → ∀ v : K, (∀ k ∈ H, ρ k v = v) → ∀ ε : ℝ, 0 < ε → ∃ η : G → ℂ, Continuous η ∧ HasCompactSupport η ∧ (∀ k ∈ H, ρ k (∫ y, η y • ρ y v ∂μ) = ∫ y, η y • ρ y v ∂μ) ∧ ‖v - ∫ y, η y • ρ y v ∂μ‖ < ε := by sorry
