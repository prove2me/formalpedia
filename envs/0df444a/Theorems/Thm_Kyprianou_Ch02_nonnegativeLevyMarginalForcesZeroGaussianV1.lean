-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativeLevyMarginalForcesZeroGaussianV1
-- name    : Kyprianou.Ch02.nonnegativeLevyMarginalForcesZeroGaussianV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:14:33.211751+00:00
-- url     : https://prove2.me/theorems/3d580909-4eaf-478a-99da-e762d6b0cb8f
-- title:
--   A nonnegative Lévy marginal forces zero Gaussian variance
-- statement:
--   Realize the zero-Gaussian triplet as a genuine Lévy process and take its time-one law. The original law is its convolution with the centred Gaussian of the prescribed variance, by characteristic-function uniqueness and the proved factorisation. A positive variance contradicts the negative-mass condition.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegativeLevyMarginalForcesZeroGaussianV1
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Iio (0 : ℝ)) = 0)
    (hchar : ∀ ξ : ℝ, charFun Q ξ = Complex.exp (Kyprianou.Ch01.levyTripleExponent T ξ)) :
    T.gaussianVariance = 0 := by
  sorry
