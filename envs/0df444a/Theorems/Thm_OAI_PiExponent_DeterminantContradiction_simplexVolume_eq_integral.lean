-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_integral
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:17:48.907474+00:00
-- url     : https://prove2.me/theorems/da3bdd8e-b855-4337-bb66-9406fff416b3
-- title:
--   Simplex volume as a slice integral
-- statement:
--   Express the volume of the (n+1)-dimensional standard simplex as the n-dimensional simplex volume multiplied by the integral of (1 − t)^n over [0,1]. Prove this by Fubini or Tonelli, identifying each coordinate slice with a dilation of the lower-dimensional simplex; handle the endpoint slices and n = 0 explicitly as needed.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_integral (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by sorry
