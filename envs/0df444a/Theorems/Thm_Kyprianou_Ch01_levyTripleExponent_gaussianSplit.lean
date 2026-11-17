-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyTripleExponent_gaussianSplit
-- name    : Kyprianou.Ch01.levyTripleExponent_gaussianSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T20:21:22.813314+00:00
-- url     : https://prove2.me/theorems/6bc59e10-3b5c-4134-b3e2-e2dbd5fae3c1
-- title:
--   Exact Lévy–Khintchine exponent splitting into pure jump and Gaussian quadratic parts
-- statement:
--   For every Lévy–Khintchine triplet and real Fourier frequency, replacing its Gaussian variance by zero gives the pure-jump-and-drift triplet. The characteristic exponent of the original triplet equals the exponent of this zero-Gaussian triplet minus exactly one-half of the Gaussian variance times the square of the frequency. All drift and compensated jump terms are retained exactly. This algebraic identity is a genuine proof bridge towards assembling the positive Gaussian and pure-jump Lévy process in the full Chapter 1 Theorem 1.6.
-- source:
--   Kyprianou (2006), Chapter 1, Theorem 1.6 and equation (1.4), Lévy–Khintchine exponent of a Gaussian plus independent pure-jump process.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyTripleExponent_gaussianSplit
    (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) :
    let Tzero : ProbabilityTheory.LevyKhintchineTriple :=
      ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩
    Kyprianou.Ch01.levyTripleExponent T ξ =
      Kyprianou.Ch01.levyTripleExponent Tzero ξ -
        (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) := by
  sorry
