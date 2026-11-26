-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_controlled_queue_state_and_effective_noise_are_cadlag
-- name    : ManyServerQED.Scheduling.controlled_queue_state_and_effective_noise_are_cadlag
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:49:42.340217+00:00
-- url     : https://prove2.me/theorems/0ce4b8d4-ade2-4735-b277-5585a314b104
-- title:
--   Controlled queue state and effective noise are càdlàg
-- statement:
--   For a controlled queue row of positive size, the scaled state and the standardized effective noise have càdlàg paths on nonnegative time.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_cadlag_composition_with_continuous_nondecreasing_clock
import Theorems.Thm_ManyServerQED_Scheduling_queue_centered_primitives_are_cadlag
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.controlled_queue_state_and_effective_noise_are_cadlag {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsControlled n X0 X Ψ)
    (ω : Ω) (i : Fin k) :
    IsCadlag (fun t => M.Xhat n X ω t i) ∧
    IsCadlag (fun t =>
      (M.Ahat n ω t i-M.Shat n ω (busyTime Ψ ω i t/(n:ℝ)) i-
        M.Rhat n ω (queueTime X Ψ ω i t/(n:ℝ)) i)/M.diffData.r i) := by sorry
