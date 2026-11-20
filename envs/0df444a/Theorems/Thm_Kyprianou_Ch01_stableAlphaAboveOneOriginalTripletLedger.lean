-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneOriginalTripletLedger
-- name    : Kyprianou.Ch01.stableAlphaAboveOneOriginalTripletLedger
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:35:18.920968+00:00
-- url     : https://prove2.me/theorems/e56a2136-8567-46a9-a5ad-cc75efcfc825
-- title:
--   Original stable Lévy triplet exponent exact Fourier ledger AboveOne
-- statement:
--   For the original positive and negative stable power-law Lévy measures, zero Gaussian variance and the source triplet exponent, prove the explicit canonical complex Fourier characteristic exponent with the exact Gamma/cosine scale and skewness ratio; its drift is the finite large-jump correction -(cpos-cneg)/(alpha-1).
-- source:
--   Kyprianou (2006) Exercise 1.4, source-exact case AboveOne and original compensation convention.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneOriginalTripletLedger
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : 1 < alpha)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) * (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((((cpos - cneg) / (cpos + cneg)) * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * ((((-T.drift - (cpos - cneg) / (alpha - 1)) * xi : ℝ) : ℂ)) := by sorry
