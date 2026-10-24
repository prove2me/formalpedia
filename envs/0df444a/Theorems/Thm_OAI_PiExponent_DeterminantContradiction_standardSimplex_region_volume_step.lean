-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_step
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:15:12.596984+00:00
-- url     : https://prove2.me/theorems/663621bb-9d23-45dd-9298-7e18a9a5b8fa
-- title:
--   Simplex volume successor step
-- statement:
--   Assuming the volume formula in dimension m at every positive radius, the formula in dimension m + 1 follows by slicing the simplex along its last coordinate and integrating the lower-dimensional slice volumes.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_step {m : Nat} (H : Real) (hH : 0 < H)
    (ih : ∀ (T : Real), 0 < T →
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ T}).toReal =
        T ^ m / ((Nat.factorial m : Nat) : Real)) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      H ^ (m + 1) / ((Nat.factorial (m + 1) : Nat) : Real) := by sorry
