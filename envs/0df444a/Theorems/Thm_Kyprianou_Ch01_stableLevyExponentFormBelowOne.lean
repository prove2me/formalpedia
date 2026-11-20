-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormBelowOne
-- name    : Kyprianou.Ch01.stableLevyExponentFormBelowOne
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:44:13.083326+00:00
-- url     : https://prove2.me/theorems/b7428540-e7e9-4cf4-9a22-24bbe2ef2309
-- title:
--   Complete stable Levy-Khintchine exponent for alpha between zero and one
-- statement:
--   Proof of stable Levy-Khintchine original two-sided jump formula for the 0<alpha<1 case with the original truncation, scale and skewness.
-- source:
--   Kyprianou (2006) Chapter 1, Exercise 1.4; original alpha not equal one exponent, split by alpha interval.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableLevyExponentFormBelowOne
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : alpha < 1)
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
