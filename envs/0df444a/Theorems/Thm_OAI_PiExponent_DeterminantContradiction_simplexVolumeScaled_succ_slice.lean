-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_slice
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:38:07.575904+00:00
-- url     : https://prove2.me/theorems/a70af012-1648-4c21-a460-e553b6806e5c
-- title:
--   Simplex volume as an integral of its coordinate slices
-- statement:
--   Express the volume of the (n+1)-dimensional simplex as the integral over its last coordinate of the volumes of the remaining n-dimensional slices. The condition hr bounds the coordinate interval; for each t in that interval, the fiber is the lower-dimensional simplex at scale r − t.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_slice (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume := by sorry
