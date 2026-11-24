-- Prove2me | Theorems.Thm_GlobalTheory_T_group_action_haar_scaling_continuous
-- name    : GlobalTheory.T.group_action_haar_scaling_continuous
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:22.025796+00:00
-- url     : https://prove2.me/theorems/7eff0300-b7c9-4a19-be74-b1259f1f9d90
-- title:
--   T: group action haar scaling continuous
-- statement:
--   The T construction uses the group action haar scaling continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GroupActionHaarScalingContinuousStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GroupActionHaarScalingContinuousStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GroupActionHaarScalingContinuous
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GroupActionHaarScalingContinuousStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.group_action_haar_scaling_continuous : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V), (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) → (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) → ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by sorry
