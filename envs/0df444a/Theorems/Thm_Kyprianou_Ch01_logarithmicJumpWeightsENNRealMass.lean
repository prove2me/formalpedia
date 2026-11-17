-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsENNRealMass
-- name    : Kyprianou.Ch01.logarithmicJumpWeightsENNRealMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:56:42.019722+00:00
-- url     : https://prove2.me/theorems/954e1526-ce7a-4bbf-925f-48126ce73747
-- title:
--   Extended-nonnegative logarithmic jump weights have probability mass one
-- statement:
--   For 0<q<1, the canonical logarithmic jump distribution on positive integers has unit total mass after embedding its weights into extended nonnegative reals. This bridges the proved real series normalisation to a probability-law construction used in Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsHasSumOne
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpWeightsENNRealMass
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∑' n : ℕ,
      ENNReal.ofReal
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q)))) = 1 := by
  sorry
