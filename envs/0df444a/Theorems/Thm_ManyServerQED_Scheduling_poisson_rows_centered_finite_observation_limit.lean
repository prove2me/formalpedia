-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_finite_observation_limit
-- name    : ManyServerQED.Scheduling.poisson_rows_centered_finite_observation_limit
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:39:02.191942+00:00
-- url     : https://prove2.me/theorems/971463f3-2fc5-5fee-b189-1aa8a5deeafc
-- title:
--   Finite-dimensional Brownian limits for centered Poisson rows
-- statement:
--   Let the rate of the $n$th independent-increment Poisson process be $a_n$, with $a_n\to a\ge0$. Observe the $n$th row at times $nt$, subtract $na_nt$, and divide by $\sqrt n$. The finite-dimensional laws converge to those of $\sqrt a$ times standard Brownian motion. The rows may have arbitrary dependence across $n$.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

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

theorem ManyServerQED.Scheduling.poisson_rows_centered_finite_observation_limit {Ω Ω₀ Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace Ω']
    {P : Measure Ω} {P₀ : Measure Ω₀} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P₀] [IsProbabilityMeasure P']
    (N : ℕ → Ω → ℝ → ℝ) (aN : ℕ → ℝ) (hN : ∀ n, IsPoissonProcess P (N n) (aN n))
    (a : ℝ) (ha : 0 ≤ a) (hconv : Tendsto aN atTop (𝓝 a))
    (N₀ : Ω₀ → ℝ → ℝ) (hN₀ : IsPoissonProcess P₀ N₀ 1)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
    TendstoInDistribution
      (fun (n : ℕ) ω j => (N n ω ((n:ℝ)*τ j) - (n:ℝ)*aN n*τ j)/Real.sqrt n)
      atTop (fun ω j => Real.sqrt a*B (τ j).toNNReal ω) (fun _ => P) P' := by sorry
