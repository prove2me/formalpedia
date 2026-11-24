-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyGaussianQuadraticLowerBoundV1
-- name    : Kyprianou.Ch02.levyGaussianQuadraticLowerBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:52:06.134385+00:00
-- url     : https://prove2.me/theorems/2096168e-52d2-4967-8ab1-a4da0f2ac138
-- title:
--   Gaussian variance gives a quadratic lower bound on the negative real exponent
-- statement:
--   Split off the Gaussian part. The remaining real exponent is nonpositive, as it is the logarithmic modulus of a characteristic function of the zero-Gaussian Lévy marginal.
-- source:
--   Kyprianou (2006), Lemma 2.12

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyGaussianQuadraticLowerBoundV1
    (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) :
    (T.gaussianVariance : ℝ) * ξ ^ 2 / 2 ≤
      -(Kyprianou.Ch01.levyTripleExponent T ξ).re := by sorry
