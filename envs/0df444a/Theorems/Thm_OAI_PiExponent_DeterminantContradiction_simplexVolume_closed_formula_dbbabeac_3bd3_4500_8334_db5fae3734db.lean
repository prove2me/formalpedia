-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:46:48.89104+00:00
-- url     : https://prove2.me/theorems/632d3db7-a987-477b-9761-021a5f422e95
-- title:
--   Closed formula for unit simplex volume
-- statement:
--   The n-dimensional nonnegative unit simplex has volume 1/n!. This is the geometric core of the reduction. An independent proof route is induction on dimension using Fubini to integrate the scaled lower-dimensional sections. At n = 0, the empty-coordinate simplex has volume 1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_closed_formula_dbbabeac_3bd3_4500_8334_db5fae3734db (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
