-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTripletIntegralSplitNonnegative
-- name    : Kyprianou.Ch01.stableAlphaOneTripletIntegralSplitNonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:58:43.035167+00:00
-- url     : https://prove2.me/theorems/dbb6a30e-90ae-47d4-bae0-14e0d0c81426
-- title:
--   Exact signed index-one Lévy compensated integral splits across positive and negative jump measures
-- statement:
--   Reduce the original signed Lévy triplet exponent to the drift term and the separate positive- and negative-halfline compensated jump integrals. Must use genuine integrability of the compensated integrand against the Lévy measure and its summands before applying additivity in measure.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4: original two-sided Levy triplet index-one compensator.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneTripletIntegralSplitNonnegative
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ) (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let alpha : ℝ := 1
    let muPos : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1)))
    let muNeg : Measure ℝ := (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
    T.gaussianVariance = 0 →
    T.levyMeasure = muPos + muNeg →
    ∀ xi : ℝ, -Kyprianou.Ch01.levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg)
      := by sorry
