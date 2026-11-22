-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_finite_measure_eq_of_positive_laplace_eq_public
-- name    : Kyprianou.Ch08.StageB.p2m81_finite_measure_eq_of_positive_laplace_eq_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T18:48:29.942548+00:00
-- url     : https://prove2.me/theorems/b25a765a-cb88-474e-b980-dc754335ac39
-- title:
--   Finite half-line measures with equal positive Laplace transforms are equal
-- statement:
--   Two finite measures supported on the nonnegative half-line and having equal extended-nonnegative Laplace transforms at every positive real rate are equal. Apply the accepted finite-measure complex-MGF uniqueness theorem to exponential tilts of both measures. The tilt makes each complex MGF analytic on a half-plane with positive boundary, and the tilted transform at real parameter t is the original Laplace transform at positive rate a-t.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Public helper for the geometric descending potential, finite-tilt uniqueness step.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_finite_measure_eq_of_positive_laplace_eq_public
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Iio (0 : ℝ)) = 0) (hν : ν (Iio (0 : ℝ)) = 0)
    (hL : ∀ s : ℝ, 0 < s →
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂μ) =
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂ν)) :
    μ = ν := by
  sorry
