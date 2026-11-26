-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_centered_queue_arrival_noise_restarted_clock_approximation
-- name    : ManyServerQED.Scheduling.centered_queue_arrival_noise_restarted_clock_approximation
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:01:07.660308+00:00
-- url     : https://prove2.me/theorems/68d0b206-0d30-4f9e-adff-5452ffa91870
-- title:
--   Centered arrivals at the next-arrival clock
-- statement:
--   On a compact calendar interval after a fixed time, restarting the centered renewal row at its next arrival changes its values by a quantity vanishing uniformly in probability.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_next_arrival_residual_vanishes
import Theorems.Thm_ManyServerQED_Scheduling_queue_arrival_norm_and_modulus_bounds
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
import Theorems.Thm_ManyServerQED_Scheduling_asymptotic_modulus_transfers_uniform_random_clock_evaluations
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.centered_queue_arrival_noise_restarted_clock_approximation {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k)
    (mL mU : ℝ) (hA3 : M.Assumption3 mL mU)
    (i : Fin k) (b : ℝ) (hb : 0 ≤ b) (T : ℝ) (hT : b ≤ T) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T,
      ε ≤ |M.Ahat n ω (M.nextArrival n i ω b+(t-b)) i-M.Ahat n ω t i|}) atTop (𝓝 0) := by sorry
