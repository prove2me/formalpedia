-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_formula
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:46:47.463241+00:00
-- url     : https://prove2.me/theorems/8d2c2eb3-5d9d-4725-8293-00b7a18005ce
-- title:
--   Closed formula for scaled simplex volume
-- statement:
--   The ENNReal volume of the nonnegative coordinate simplex of scale r is the ENNReal coercion of r^n/n!. This includes dimension zero and scale zero.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_formula (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n / (Nat.factorial n : Real)) := by sorry
