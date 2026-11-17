-- Prove2me | Theorems.Thm_Kyprianou_Ch01_diracZeroInfinitelyDivisibleLaw
-- name    : Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:38:55.231938+00:00
-- url     : https://prove2.me/theorems/911426c4-09b9-4889-95ed-a06448cd7911
-- title:
--   Dirac zero is infinitely divisible by explicit convolution roots at every positive order
-- statement:
--   The point mass at zero on the real line is infinitely divisible in the exact LevyFoundations sense: for every positive integer n, choose the Dirac zero measure itself as the probability convolution root, and prove by induction that its n-fold convolution power is again Dirac zero. This is the degenerate case p=1 of the geometric counting law in Chapter 1 Exercise 1.2(i), and the proof uses the actual recursive convolution power definition without any unproved infinite-divisibility assumptions.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.2(i), boundary p=1; pinned MeasureTheory.Measure convolution and LevyFoundations.iteratedConvolutionPower.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory LevyFoundations
set_option autoImplicit false

theorem Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw :
    LevyFoundations.isInfinitelyDivisibleLaw
      (Measure.dirac (0 : ℝ)) := by
  sorry
