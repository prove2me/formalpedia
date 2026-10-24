-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_of_lower
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_of_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:29:09.39199+00:00
-- url     : https://prove2.me/theorems/e741f1df-6457-4a86-9328-6dd31228691d
-- title:
--   Successor-dimensional simplex volume from all lower-dimensional scales
-- statement:
--   Assuming the volume formula in dimension `n` for every nonnegative scale, derive it in dimension `n + 1` by slicing off one coordinate, applying Fubini to the lower-dimensional fibers, and integrating the resulting power. This removes the full successor-step argument from the parent induction; its independent proof route is the coordinate decomposition and simplex-slice calculation followed by the elementary power integral.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_of_lower
    (n : Nat) (r : Real) (hr : 0 ≤ r)
    (ih : ∀ s : Real, 0 ≤ s →
      MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ s} =
        ENNReal.ofReal (s ^ n / (Nat.factorial n : Real))) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by sorry
