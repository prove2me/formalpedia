-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_region_volume
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_region_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:02:37.202091+00:00
-- url     : https://prove2.me/theorems/a8f2f25f-7998-4701-a3f3-4adcbc337c9c
-- title:
--   Real volume of a positive weighted simplex
-- statement:
--   The real-valued Lebesgue volume of the nonnegative region with positive weighted sum at most H is H^m divided by m! and the product of the coordinate weights.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_region_volume {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}).toReal =
      H ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by sorry
