-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveDeficitSquaredDensityInjective
-- name    : Kyprianou.Ch05.positiveDeficitSquaredDensityInjective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T13:03:16.878027+00:00
-- url     : https://prove2.me/theorems/4803f600-c857-5840-854e-9e6b2ec679c9
-- title:
--   Positive jump measures recovered from squared-deficit weighted measures
-- statement:
--   Replace the weight off the positive half-line by one, where both measures vanish. Apply Avram everywhere-positive finite-density injectivity.
-- source:
--   Kyprianou (2006), Exercise 5.6(i); weighted Laplace transform.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.positiveDeficitSquaredDensityInjective
    (mu nu : Measure Real)
    (hm : mu (Set.Iic (0 : Real)) = 0)
    (hn : nu (Set.Iic (0 : Real)) = 0)
    (heq : mu.withDensity (fun x => ENNReal.ofReal ((1 - Real.exp (-x)) ^ 2)) =
      nu.withDensity (fun x => ENNReal.ofReal ((1 - Real.exp (-x)) ^ 2))) :
    mu = nu := by
  sorry
