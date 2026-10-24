-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_boundary
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_boundary
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:06:40.677389+00:00
-- url     : https://prove2.me/theorems/cfd7422a-e0d5-4730-9c7c-df5121ecd4ad
-- title:
--   Boundary cases for coordinate simplex scaling
-- statement:
--   The scaling identity holds when the dimension is zero or the scale is zero. In dimension zero the coordinate space is a singleton and the exponent is zero. At zero scale in positive dimension, nonnegative coordinates with sum at most zero form `{0}`, whose volume is zero.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_boundary (n : Nat) (r : Real) (hr : 0 ≤ r) (hboundary : n = 0 ∨ r = 0) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by sorry
