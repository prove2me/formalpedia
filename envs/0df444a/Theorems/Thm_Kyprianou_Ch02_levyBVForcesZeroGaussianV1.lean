-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyBVForcesZeroGaussianV1
-- name    : Kyprianou.Ch02.levyBVForcesZeroGaussianV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:37:57.156835+00:00
-- url     : https://prove2.me/theorems/e578fc02-04b3-4435-8b1f-fa76673b4306
-- title:
--   Almost-sure bounded-variation Lévy paths force zero Gaussian variance
-- statement:
--   The process-level necessity that a real Lévy process with almost surely locally bounded-variation trajectories has no nonzero Brownian/Gaussian component. It must use Gaussian quadratic variation and source-faithful independent jump decomposition or a valid process-level characteristic-triplet uniqueness argument.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyBVForcesZeroGaussianV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) →
    σ = 0 := by
  sorry
