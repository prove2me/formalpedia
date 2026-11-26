-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_interval_modulus_bound
-- name    : ManyServerQED.Scheduling.poisson_rows_centered_interval_modulus_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:42:56.455931+00:00
-- url     : https://prove2.me/theorems/aeaddef1-6de7-55dc-9ba7-e4df8d277b9e
-- title:
--   Uniform modulus bound for centered Poisson rows
-- statement:
--   For Poisson processes whose row rates converge to a finite nonnegative limit, the centered processes evaluated at time n times t and divided by the square root of n have an asymptotically small uniform modulus of continuity on each integer horizon. The rows may be dependent across n.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus
import Theorems.Thm_ManyServerQED_Scheduling_poisson_polygonal_interpolation_uniform_error
import Theorems.Thm_ManyServerQED_Scheduling_centered_scaled_poisson_finite_dimensional_convergence
import Theorems.Thm_ManyServerQED_Scheduling_poisson_path_laws_with_matched_time_scales
import Theorems.Thm_ManyServerQED_Scheduling_brownian_weighted_finite_observation_law
import Theorems.Thm_DurrettProbability_donsker
import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling DurrettProbability
open Set Finset
open BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.poisson_rows_centered_interval_modulus_bound {Ω Ω₀ Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace Ω']
    {P : Measure Ω} {P₀ : Measure Ω₀} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P₀] [IsProbabilityMeasure P']
    (N : ℕ → Ω → ℝ → ℝ) (aN : ℕ → ℝ) (hN : ∀ n, IsPoissonProcess P (N n) (aN n))
    (a : ℝ) (ha : 0 ≤ a) (hconv : Tendsto aN atTop (𝓝 a))
    (N₀ : Ω₀ → ℝ → ℝ) (hN₀ : IsPoissonProcess P₀ N₀ 1)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    let Q (n : ℕ) (ω : Ω) (t : ℝ) :=
      (N n ω ((n:ℝ)*t) - (n:ℝ)*aN n*t)/Real.sqrt n
    ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
          ε ≤ |Q n ω s - Q n ω t|} ≤ ENNReal.ofReal η := by sorry
