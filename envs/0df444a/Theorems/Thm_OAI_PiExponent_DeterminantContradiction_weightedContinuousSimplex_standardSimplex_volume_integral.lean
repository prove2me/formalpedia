-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedContinuousSimplex_standardSimplex_volume_integral
-- name    : OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:49:18.323223+00:00
-- url     : https://prove2.me/theorems/5d77e15d-7c5a-49c0-9cf1-a6aae47dc07c
-- title:
--   Simplex power integral
-- statement:
--   For positive `T`, the integral of the dimension-`n` slice formula over `0 < t < T` equals the dimension-`n+1` simplex volume formula.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_standardSimplex_volume_integral (n : Nat) (T : Real) (hT : 0 < T) : (∫⁻ t in Set.Ioo (0 : Real) T, ENNReal.ofReal ((T - t) ^ n / (n.factorial : Real)) ∂MeasureTheory.volume) = ENNReal.ofReal (T ^ (n + 1) / ((n + 1).factorial : Real)) := by sorry
