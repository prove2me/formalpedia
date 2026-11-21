-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
-- name    : Kyprianou.Ch08.StageB.source_result81_exponent_quadratic_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T14:20:25.797006+00:00
-- url     : https://prove2.me/theorems/ca3f7cac-acf6-4a05-8eae-e40f37fe426f
-- title:
--   Quadratic upper bound on the actual nonnegative Laplace exponent
-- statement:
--   Use the law-consistent triplet formula. On negative small jumps the compensated exponential is bounded by one half of the squared argument, and on large negative jumps it is nonpositive. The drift and Gaussian terms then give the quadratic bound.
-- source:
--   Kyprianou (2006), Chapter 8, Laplace normalization (8.5). Decomposition of 4a5bedc9-ffce-4d0e-abf0-74c2a8cddb49.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_exponent_quadratic_upper
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℝ, 1 ≤ β → ψ β ≤ K * β ^ 2 := by
  sorry
