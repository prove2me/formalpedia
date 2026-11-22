-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormAwayFromOne
-- name    : Kyprianou.Ch01.stableLevyExponentFormAwayFromOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:07:52.521045+00:00
-- url     : https://prove2.me/theorems/14129268-8e81-434d-ac80-084d68b6b631
-- title:
--   Exercise 1.4: stable Lévy–Khintchine formula for indices other than one
-- statement:
--   Derive the complete stable characteristic exponent (1.7) from the two-sided power-law Lévy measure, including scale, skewness from positive and negative intensity ratios, and the drift correction. Covers 0<alpha<1 and 1<alpha<2.
-- source:
--   Kyprianou (2006), §1.2.6 equation (1.7), Exercise 1.4(i),(iii).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableLevyExponentFormAwayFromOne
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
