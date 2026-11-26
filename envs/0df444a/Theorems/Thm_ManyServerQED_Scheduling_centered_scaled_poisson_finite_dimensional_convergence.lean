-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_centered_scaled_poisson_finite_dimensional_convergence
-- name    : ManyServerQED.Scheduling.centered_scaled_poisson_finite_dimensional_convergence
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-26T01:08:51.694253+00:00
-- url     : https://prove2.me/theorems/939bac75-5f7a-4436-849e-16f7c48fd415
-- title:
--   Finite-dimensional Poisson convergence at varying rates
-- statement:
--   Let a sequence of nonnegative time-scale coefficients converge. The corresponding diffusively scaled centered rate-one Poisson counts converge jointly at any finite list of nonnegative observation times to the Brownian values with the corresponding deterministic time scaling.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_DurrettProbability_donsker
import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling DurrettProbability
open Set Finset
open scoped ENNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.centered_scaled_poisson_finite_dimensional_convergence {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (N : Ω → ℝ → ℝ) (hN : IsPoissonProcess P N 1)
    (hId : ∀ j : ℕ, IdentDistrib (fun ω => N ω ((j:ℝ)+1) - N ω j) (fun ω => N ω 1) P P)
    (hSq : Integrable (fun ω => (N ω 1)^2) P)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (a : ℝ) (ha : 0 ≤ a)
    (haL : Tendsto aN atTop (𝓝 a))
    (T : ℝ) (hT : 0 ≤ T) (J : ℕ) (hJ : (a+1)*(T+1) < J)
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ i, τ i ∈ Icc (0:ℝ) T)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω i => (N ω ((n:ℝ)*aN n*τ i) - (n:ℝ)*aN n*τ i)/Real.sqrt n)
      atTop (fun ω i => Real.sqrt (J:ℝ) * B ((a*τ i/(J:ℝ)).toNNReal) ω) (fun _ => P) P' := by sorry
