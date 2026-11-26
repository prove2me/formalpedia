-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_state_and_allocation_jointly_measurable_in_past
-- name    : ManyServerQED.Scheduling.queue_state_and_allocation_jointly_measurable_in_past
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:57:50.014579+00:00
-- url     : https://prove2.me/theorems/907568d4-722d-4091-93cf-5f775e67eb04
-- title:
--   Joint measurability of bounded-horizon queue paths in past information
-- statement:
--   For a fixed horizon, the queue state and service allocation evaluated at time clipped to that horizon are jointly measurable in the past information at the horizon and the time argument.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Mathlib
open Set MeasureTheory Filter Topology
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped NNReal

theorem ManyServerQED.Scheduling.queue_state_and_allocation_jointly_measurable_in_past {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hSCP : M.IsSCP n X0 X Ψ)
    (T : ℝ≥0) :
    @Measurable (Ω × ℝ≥0) (Fin k → ℝ)
      (@MeasurableSpace.prod Ω ℝ≥0 (M.pastInfo n X Ψ T) inferInstance)
      inferInstance (fun z => X z.1 (min (z.2:ℝ) T)) ∧
    @Measurable (Ω × ℝ≥0) (Fin k → ℝ)
      (@MeasurableSpace.prod Ω ℝ≥0 (M.pastInfo n X Ψ T) inferInstance)
      inferInstance (fun z => Ψ z.1 (min (z.2:ℝ) T)) := by sorry
