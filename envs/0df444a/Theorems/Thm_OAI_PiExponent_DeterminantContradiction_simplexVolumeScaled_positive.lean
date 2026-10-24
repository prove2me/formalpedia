-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_positive
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_positive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:06:59.195185+00:00
-- url     : https://prove2.me/theorems/cd90c11c-c3ac-4bd0-9c5e-71cc898d9fc2
-- title:
--   Positive-scale coordinate simplex scaling
-- statement:
--   For positive scale, the simplex of scale `r` is the preimage of the unit simplex under scalar multiplication by `1/r`. Establish measurability of the unit simplex, apply the linear-map volume change-of-variables theorem, and compute the scalar map's determinant as `(1/r)^n`, yielding the factor `r^n`.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_positive (n : Nat) (r : Real) (hr : 0 ≤ r) (hpos : 0 < r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by sorry
