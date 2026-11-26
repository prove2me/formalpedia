-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_past_generators_are_ambient_measurable
-- name    : ManyServerQED.Scheduling.queue_past_generators_are_ambient_measurable
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-26T04:48:15.672834+00:00
-- url     : https://prove2.me/theorems/77ece076-8f6c-4553-872f-40ea1aa7d6e3
-- title:
--   Ambient measurability of individual queue past observations
-- statement:
--   At a fixed nonnegative time in a controlled queue row, the arrival count, service count at the service clock, abandonment count at the queue clock, queue length, allocation and state are measurable in the ambient probability space.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_scp_joint_state_measurable
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_past_generators_are_ambient_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X₀ : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsSCP n X₀ X Ψ)
    (i : Fin k) (T : ℝ) (hT : 0 ≤ T) :
    Measurable (fun ω => M.A n i ω T) ∧
      Measurable (fun ω => M.S n i ω (busyTime Ψ ω i T)) ∧
      Measurable (fun ω => M.R n i ω (queueTime X Ψ ω i T)) ∧
      Measurable (fun ω => X ω T i-Ψ ω T i) ∧
      Measurable (fun ω => Ψ ω T i) ∧ Measurable (fun ω => X ω T i) := by sorry
