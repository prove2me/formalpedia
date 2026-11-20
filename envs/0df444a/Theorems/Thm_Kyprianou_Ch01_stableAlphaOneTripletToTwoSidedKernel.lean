-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTripletToTwoSidedKernel
-- name    : Kyprianou.Ch01.stableAlphaOneTripletToTwoSidedKernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:52:09.858035+00:00
-- url     : https://prove2.me/theorems/aa311b51-88a8-42ba-9db4-0efc250886c7
-- title:
--   Alpha-one original two-sided Levy-Khintchine triplet equals weighted compensated oscillatory kernels
-- statement:
--   For the exact original index-one two-sided Lévy power-law measure and zero Gaussian variance, the signed Lévy–Khintchine exponent equals negative drift plus the positive and reflected-negative compensated oscillatory kernels with their original cpos,cneg multipliers. Includes the precise truncation 1_{r<1}, measure reflection and pointwise 1/r² identity.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, alpha one: original two-sided Levy jump integral reduction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneTripletToTwoSidedKernel
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ) :
    let alpha : ℝ := 1
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
    let F : ℝ → ℂ := fun xi =>
      ∫ r in Set.Ioi (0 : ℝ),
        ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
            Complex.I * (((xi * r : ℝ) : ℂ)) *
              (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∀ xi : ℝ,
      -Kyprianou.Ch01.levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
        (cpos : ℂ) * F xi + (cneg : ℂ) * F (-xi) := by sorry
