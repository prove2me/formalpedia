-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsHasSumOne
-- name    : Kyprianou.Ch01.logarithmicJumpWeightsHasSumOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:50:40.036838+00:00
-- url     : https://prove2.me/theorems/46671777-a08e-48d7-805b-5efff5f7b6d2
-- title:
--   Logarithmic jump weights sum to one for the strict geometric compound-Poisson representation
-- statement:
--   For any real 0<q<1, the positive logarithmic-series weights q^(n+1)/((n+1)(-log(1-q))) sum to one. This makes the jump-count weights a probability mass function, a source-backed prerequisite for the compound-Poisson construction in Kyprianou (2006), Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i) and its solutions; uses public Kyprianou.Ch01.realLogSeriesMass.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_realLogSeriesMass
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpWeightsHasSumOne (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ =>
        (q ^ (n + 1) / ((n : ℝ) + 1)) /
          (-Real.log (1 - q))) 1 := by
  sorry
