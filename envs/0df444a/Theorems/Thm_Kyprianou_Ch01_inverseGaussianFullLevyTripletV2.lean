-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianFullLevyTripletV2
-- name    : Kyprianou.Ch01.inverseGaussianFullLevyTripletV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T14:23:40.344828+00:00
-- url     : https://prove2.me/theorems/17f9c492-b146-449f-b81c-f7ccee23f889
-- title:
--   Exercise 1.6(ii): complete inverse Gaussian Lévy triplet and compensated drift
-- statement:
--   Identify the Gaussian coefficient, scaled Lévy measure, and truncation-dependent drift of the inverse Gaussian time-s marginal as required by the book.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.6(ii), printed p. 29–30, triplet (a, σ, Π) for inverse Gaussian τ_s.

import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.inverseGaussianFullLevyTripletV2
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))));
    let drift : ℝ :=
      -(2 * s / b) *
        (∫ y in (0 : ℝ)..b,
          Real.exp (-(y ^ 2 / 2)) / Real.sqrt (2 * Real.pi) ∂volume);
    (s * ∫ x in Set.Ioo (0 : ℝ) (1 : ℝ), x ∂Pi) = -drift ∧
      ∃ T : ProbabilityTheory.LevyKhintchineTriple,
        T.gaussianVariance = 0 ∧
          T.levyMeasure = (ENNReal.ofReal s) • Pi ∧
          T.drift = drift := by
  sorry
