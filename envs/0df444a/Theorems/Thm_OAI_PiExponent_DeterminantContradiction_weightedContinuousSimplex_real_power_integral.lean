-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_real_power_integral
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_real_power_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:47:42.61849+00:00
-- url     : https://prove2.me/theorems/2f352c2e-78dd-4fca-bec7-3bfa9c4d0439
-- title:
--   Real simplex power integral
-- statement:
--   For natural `n` and positive `T`, integrating `(T - t)^n / n!` over `(0,T)` gives `T^(n+1)/(n+1)!`. The antiderivative and factorial recurrence provide a direct proof route.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_real_power_integral (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo (0 : Real) T)) (fun t : Real => (T - t) ^ n / (n.factorial : Real)) = T ^ (n + 1) / ((n + 1).factorial : Real) := by sorry
