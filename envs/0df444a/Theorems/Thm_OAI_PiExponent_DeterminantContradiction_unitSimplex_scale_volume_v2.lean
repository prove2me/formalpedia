-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplex_scale_volume_v2
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplex_scale_volume_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:30:03.474131+00:00
-- url     : https://prove2.me/theorems/ece1474a-995b-4e95-abf1-9925481171c5
-- title:
--   Scaling the coordinate simplex
-- statement:
--   Scaling the unit coordinate simplex by a nonnegative real s multiplies its volume by s to the n, including zero scale and dimension zero.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplex_scale_volume_v2 (n : Nat) (s : Real) (hs : 0 ≤ s) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ s} =
    ENNReal.ofReal (s ^ n) *
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} := by sorry
