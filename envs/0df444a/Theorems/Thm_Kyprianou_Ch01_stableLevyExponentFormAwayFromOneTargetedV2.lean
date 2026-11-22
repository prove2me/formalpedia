-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormAwayFromOneTargetedV2
-- name    : Kyprianou.Ch01.stableLevyExponentFormAwayFromOneTargetedV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T20:10:26.245198+00:00
-- url     : https://prove2.me/theorems/dda7d983-f583-427b-b401-4bd6e884b735
-- title:
--   Stable Lévy exponent formula away from index one with targeted triplet imports
-- statement:
--   The full source-exact stable Lévy exponent representation for 0<alpha<2, alpha not equal to 1, nonnegative positive/negative jump-density coefficients with positive sum, and the specified zero-Gaussian Lévy measure. The theorem keeps the same parameters, normalization, skewness, and existential linear drift correction as the existing Chapter 1 theorem 14129268-8e81-434d-ac80-084d68b6b631. Only the theorem declaration name and mathematically identical published targeted exponent Definition import have changed. This avoids a demonstrably incompatible legacy Definition import when assembling the chapter-wide proof.
-- source:
--   Kyprianou (2006), Chapter 1, stable-process characteristic exponents, Section 1.2.6; original global theorem 14129268-8e81-434d-ac80-084d68b6b631.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableLevyExponentFormAwayFromOneTargetedV2
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : alpha ≠ 1)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          ((c * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((beta * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
  sorry
