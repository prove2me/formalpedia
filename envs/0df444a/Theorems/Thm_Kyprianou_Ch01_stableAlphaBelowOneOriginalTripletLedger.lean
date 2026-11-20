-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneOriginalTripletLedger
-- name    : Kyprianou.Ch01.stableAlphaBelowOneOriginalTripletLedger
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:35:08.093691+00:00
-- url     : https://prove2.me/theorems/90403905-2cc4-40b4-8f23-13706a3c82b5
-- title:
--   Original stable Lévy triplet exponent exact Fourier ledger BelowOne
-- statement:
--   For the original positive and negative stable power-law Lévy measures, zero Gaussian variance and the source triplet exponent, prove the explicit canonical complex Fourier characteristic exponent with the exact Gamma/cosine scale and skewness ratio; its drift is the finite small-jump correction (cpos-cneg)/(1-alpha).
-- source:
--   Kyprianou (2006) Exercise 1.4, source-exact case BelowOne and original compensation convention.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneOriginalTripletLedger
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
    ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) * (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((((cpos - cneg) / (cpos + cneg)) * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * (((((cpos - cneg) / (1 - alpha) - T.drift) * xi : ℝ) : ℂ)) := by sorry
