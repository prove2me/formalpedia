-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableBelowOneOriginalTripletGammaLedger
-- name    : Kyprianou.Ch01.stableBelowOneOriginalTripletGammaLedger
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:37:56.665541+00:00
-- url     : https://prove2.me/theorems/ddb5a31f-0c7a-41ad-961f-5bf5db3954f5
-- title:
--   Original below-one stable Lévy triplet exponent reduced to two Gamma Fourier powers
-- statement:
--   Evaluate the source-exact two-sided original Lévy triplet exponent as a sum of the positive and reflected Gamma fractional-power Fourier kernels plus the exact source cutoff drift correction for 0<alpha<1. No extra integrability or changed measure assumptions.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, original stable Levy-Khintchine.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableBelowOneOriginalTripletGammaLedger
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
  Complex.exp ((alpha : ℂ) *
    Complex.log (-(Complex.I * (z : ℂ)))));
    T.gaussianVariance = 0 → T.levyMeasure = Pi →
    ∀ xi : ℝ,
      -levyTripleExponent T xi =
        -((Real.Gamma (-alpha) : ℝ) : ℂ) *
          ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) +
        Complex.I * (((((cpos - cneg) / (1 - alpha) -
          T.drift) * xi : ℝ) : ℂ)) := by sorry
