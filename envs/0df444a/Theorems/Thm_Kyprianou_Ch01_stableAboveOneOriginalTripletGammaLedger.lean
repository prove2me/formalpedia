-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneOriginalTripletGammaLedger
-- name    : Kyprianou.Ch01.stableAboveOneOriginalTripletGammaLedger
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T23:49:18.332276+00:00
-- url     : https://prove2.me/theorems/c0fa6e50-0663-4fde-bc94-00102ade95aa
-- title:
--   Original above-one two-sided stable Lévy triplet Gamma Fourier ledger with large-jump compensation
-- statement:
--   Under the original two-sided stable power-law Lévy measure and zero Gaussian variance with 1<alpha<2, evaluate the exact Lévy–Khintchine exponent as a sum of positive and negative principal Gamma fractional powers, with the source cutoff compensation giving drift correction -(cpos-cneg)/(alpha-1). Include xi=0 explicitly.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4, original stable triplet exponent for 1<alpha<2.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneOriginalTripletGammaLedger
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
      Complex.exp ((alpha : ℂ) * Complex.log (-(Complex.I * (z : ℂ)))));
    T.gaussianVariance = 0 → T.levyMeasure = Pi →
    ∀ xi : ℝ,
      -levyTripleExponent T xi =
        -((Real.Gamma (-alpha) : ℝ) : ℂ) *
          ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) +
        Complex.I * ((((-T.drift - (cpos - cneg) / (alpha - 1)) * xi : ℝ) : ℂ)) := by sorry
