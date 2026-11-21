-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_triplet_finite_jump_approximation
-- name    : Kyprianou.Ch08.StageB.source_result81_triplet_finite_jump_approximation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:42:45.188109+00:00
-- url     : https://prove2.me/theorems/987aeaac-dbe6-4ff6-aca6-d87cd87bffde
-- title:
--   Finite-jump approximation of a spectrally negative triplet
-- statement:
--   Discard jumps of absolute size less than a positive cutoff tending to zero, retaining the Gaussian part and compensating the drift of the retained small jumps. The resulting Gaussian and compound-Poisson laws have characteristic functions tending to the characteristic exponent of the triplet. Their nonnegative exponential moments tend to the exponential of the corresponding compensated real exponent.
-- source:
--   Lévy–Khintchine cutoff argument for Kyprianou, Chapter 8, Theorem 8.1. Parent Prove2Me theorem 99139220-c85a-4a27-bbce-f437a4e7240e.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch08
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_triplet_finite_jump_approximation
    (T : LevyKhintchineTriple) (hneg : T.levyMeasure (Set.Ici (0 : ℝ)) = 0)
    (σ : ℝ) (hσ : σ ^ 2 = (T.gaussianVariance : ℝ)) (t : ℝ≥0) :
    ∃ μs : ℕ → ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop
        (nhds (Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ)))) ∧
      (∀ β : ℝ, 0 ≤ β →
        (∀ n, Integrable (fun x => Real.exp (β * x)) (μs n : Measure ℝ)) ∧
        Tendsto (fun n => ∫ x, Real.exp (β * x) ∂(μs n : Measure ℝ)) atTop
          (nhds (Real.exp ((t : ℝ) * tripletLaplace (-T.drift) σ T.levyMeasure β)))) := by
  sorry
