-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial_succ_step
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_succ_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:06:42.2072+00:00
-- url     : https://prove2.me/theorems/93d6f6ba-5042-42aa-8b30-6800e5eec336
-- title:
--   Simplex volume factorial successor step
-- statement:
--   Given the formula in dimension `n`, derive it in dimension `n+1` by integrating the volumes of the last-coordinate slices. Each slice below the endpoint is a dilation of the `n`-simplex by `1-t`, and the resulting integral yields the factorial recurrence.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_succ_step (n : Nat)
    (h : MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
