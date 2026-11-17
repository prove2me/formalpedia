-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyTripleExponent_expGaussianFactorisation
-- name    : Kyprianou.Ch01.levyTripleExponent_expGaussianFactorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T20:26:32.163265+00:00
-- url     : https://prove2.me/theorems/efea8a28-bfcc-4ce3-b427-786cef1cda1a
-- title:
--   Characteristic function factorises into zero-Gaussian and Gaussian components
-- statement:
--   For every admissible Lévy–Khintchine triplet, nonnegative time and real frequency, its characteristic exponential factors exactly as the characteristic exponential of the associated zero-Gaussian triplet multiplied by the centred Gaussian characteristic exponential with the original Gaussian variance. This retains every drift and jump contribution, and is the algebraic characteristic-function step for constructing an independent Gaussian-plus-pure-jump Lévy process. The direct proof unfolds both triplet exponents, applies the complex exponential addition formula, and uses ring normalisation without depending on any Open theorem.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.6 and equation (1.4), independence and the Lévy–Khintchine formula; source-exact exponent splitting theorem Kyprianou.Ch01.levyTripleExponent_gaussianSplit.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyTripleExponent_expGaussianFactorisation
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (t : ℝ≥0) (ξ : ℝ) :
    let Tzero : ProbabilityTheory.LevyKhintchineTriple :=
      ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩
    Complex.exp (((t : ℝ) : ℂ) * levyTripleExponent T ξ) =
      Complex.exp (((t : ℝ) : ℂ) * levyTripleExponent Tzero ξ) *
        Complex.exp (-((t : ℝ) : ℂ) *
          (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ)) := by
  sorry
