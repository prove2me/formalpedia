-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormIndexOne
-- name    : Kyprianou.Ch01.stableLevyExponentFormIndexOne
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:07:55.187537+00:00
-- url     : https://prove2.me/theorems/802ca6d6-48be-4ce7-bad9-dffd367b9cff
-- title:
--   Exercise 1.4: stable Lévy–Khintchine logarithmic formula at index one
-- statement:
--   Derive the index-one stable characteristic exponent (1.8) from the two-sided x^-2 Lévy density, retaining the logarithmic phase, skewness and additive drift. Includes the symmetric Cauchy case.
-- source:
--   Kyprianou (2006), §1.2.6 equation (1.8), Exercise 1.4(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableLevyExponentFormIndexOne
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
    let alpha : ℝ := 1;
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
          ((c * |xi| : ℝ) : ℂ) *
            (1 + Complex.I *
              (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
  sorry
