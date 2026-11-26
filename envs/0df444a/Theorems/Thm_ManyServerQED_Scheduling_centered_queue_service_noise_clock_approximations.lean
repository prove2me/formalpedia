-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_centered_queue_service_noise_clock_approximations
-- name    : ManyServerQED.Scheduling.centered_queue_service_noise_clock_approximations
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:50:08.044434+00:00
-- url     : https://prove2.me/theorems/812d5c3d-68a6-50ec-a69c-8535c67b6fd7
-- title:
--   Centered service noise at fluid and restarted clocks
-- statement:
--   For work-conserving queue rows, the centered service noise at the scaled cumulative busy time is uniformly close in probability on each compact interval to its value at the fluid service clock. On an interval starting at a fixed base time, it is also uniformly close to its value at a clock restarted from the actual busy time at the base, then advanced at the fluid rate.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_queue_time_changes_uoc
import Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_interval_modulus_bound
import Theorems.Thm_ManyServerQED_Scheduling_poisson_primitive_deterministic_clock_change
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
import Theorems.Thm_ManyServerQED_Scheduling_asymptotic_modulus_transfers_uniform_random_clock_evaluations
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.centered_queue_service_noise_clock_approximations {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (i : Fin k) (b : ℝ) (hb : 0 ≤ b) (T : ℝ) (hT : b ≤ T) :
    let a (n : ℕ) (ω : Ω) (t : ℝ) := busyTime (Ψ n) ω i t / (n:ℝ)
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤
        |M.Shat n ω (a n ω t) i - M.Shat n ω (M.rho i*t) i|}) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤
        |M.Shat n ω (a n ω t) i -
          M.Shat n ω (a n ω b+M.rho i*(t-b)) i|}) atTop (𝓝 0) := by sorry
