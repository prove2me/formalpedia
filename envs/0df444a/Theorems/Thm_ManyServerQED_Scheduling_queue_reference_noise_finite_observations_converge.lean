-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_reference_noise_finite_observations_converge
-- name    : ManyServerQED.Scheduling.queue_reference_noise_finite_observations_converge
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:01:10.966732+00:00
-- url     : https://prove2.me/theorems/163f7546-f513-459c-8075-c8f1e26d0a1f
-- title:
--   Finite-dimensional convergence of the reference queue noise
-- statement:
--   The normalized difference of centered arrivals at calendar times and centered services at their fluid clocks converges in finite-dimensional distribution to the corresponding difference of the weighted primitive Brownian coordinates.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_queue_primitives_joint_finite_observation_limit
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_reference_noise_finite_observations_converge {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) {P' : Measure Ω'} [IsProbabilityMeasure P']
    (B : Fin (k+k+k) → ℝ≥0 → Ω' → ℝ)
    (hB : ∀ j, IsBrownianReal (B j) P') (hBc : ∀ j ω, Continuous (fun t => B j t ω))
    (hI : iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P')
    {m : ℕ} (τ : Fin m → ℝ≥0) :
    letI := M.isProb
    TendstoInDistribution
      (fun n ω j i => (M.Ahat n ω (τ j) i - M.Shat n ω (M.rho i*(τ j:ℝ)) i)/M.diffData.r i)
      atTop (fun ω j i =>
        (Real.sqrt (M.lam i*M.cU2 i)*B (Fin.castAdd k (Fin.castAdd k i)) (τ j) ω -
          Real.sqrt (M.mu i)*B (Fin.castAdd k (Fin.natAdd k i)) ((M.rho i).toNNReal * τ j) ω) /
          M.diffData.r i) (fun _ => M.P) P' := by sorry
