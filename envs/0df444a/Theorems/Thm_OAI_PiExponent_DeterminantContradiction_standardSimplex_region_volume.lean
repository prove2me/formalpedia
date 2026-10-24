-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:09:56.897686+00:00
-- url     : https://prove2.me/theorems/af5e9495-6a46-444a-8aa8-d118bab4b233
-- title:
--   Volume of the unweighted positive simplex
-- statement:
--   The real volume of the nonnegative simplex with coordinate sum at most positive `H` is `H^m / m!`.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume {m : Nat} (H : Real) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      H ^ m / ((Nat.factorial m : Nat) : Real) := by sorry
