-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_scale
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:52:21.985906+00:00
-- url     : https://prove2.me/theorems/49dc592e-5f14-4c57-8344-bf52ca2df4f3
-- title:
--   Dilation law for the coordinate simplex
-- statement:
--   Scaling the nonnegative coordinate simplex from scale 1 to scale r multiplies its volume by r^n, including zero scale and dimension zero.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_scale (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by sorry
