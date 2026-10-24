-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_unit
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_unit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:52:39.181113+00:00
-- url     : https://prove2.me/theorems/9fab8872-24ac-43cb-95b0-a1a9c29f8298
-- title:
--   Unit coordinate simplex volume
-- statement:
--   The unit nonnegative coordinate simplex in dimension n has volume 1 divided by n factorial.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_unit (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
