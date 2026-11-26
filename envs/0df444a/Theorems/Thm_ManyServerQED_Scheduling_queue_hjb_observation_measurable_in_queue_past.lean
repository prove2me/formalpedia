-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_measurable_in_queue_past
-- name    : ManyServerQED.Scheduling.queue_hjb_observation_measurable_in_queue_past
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:42:04.898239+00:00
-- url     : https://prove2.me/theorems/3d4cf5f4-df93-5985-ac06-69429fed7b41
-- title:
--   Joint HJB observations are measurable in the queue past
-- statement:
--   For an admissible queue row, evaluating the five HJB observations at any time up to the cutoff is measurable for the queue information available at the cutoff.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_state_and_allocation_jointly_measurable_in_past
open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_observation_measurable_in_queue_past {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (hL : Continuous (Function.uncurry L))
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData L γ f)
    (n : ℕ) (hn : 1 ≤ n) (X₀ : Fin k → ℕ)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (hC : M.IsSCP n X₀ (X n) (Ψ n))
    (T t : ℝ≥0) (ht : t ≤ T) :
    @Measurable Ω (Fin (k+k+k+2) → ℝ) (M.pastInfo n (X n) (Ψ n) T) inferInstance
      (fun ω => queueHJBObservation M L γ u0 f X Ψ n ω t) := by sorry
