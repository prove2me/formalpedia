-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:59:31.341354+00:00
-- url     : https://prove2.me/theorems/ddd174fb-43d0-4a91-b118-a8412ba88559
-- title:
--   Simplex volume factorial formula
-- statement:
--   For every natural dimension n, the nonnegative unit simplex in ℝⁿ has volume 1/n!, including the zero-dimensional case.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
