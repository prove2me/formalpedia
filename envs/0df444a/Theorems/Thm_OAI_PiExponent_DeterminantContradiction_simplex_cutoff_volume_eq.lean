-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_eq
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:48:40.548204+00:00
-- url     : https://prove2.me/theorems/e60ff53e-5d35-43ff-a1b1-1845e380cb0f
-- title:
--   Volume scaling for a nonnegative simplex cutoff
-- statement:
--   For every finite dimension and nonnegative cutoff r, the volume of the coordinatewise nonnegative simplex with coordinate sum at most r is the unit simplex volume multiplied by r to the dimension. The case r = 0 is included.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_eq
    (n : Nat) (r : Real) (hr : 0 ≤ r) :
    (MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ r}).toReal =
      (MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
        ∑ i : Fin n, y i ≤ 1}).toReal * r ^ n := by
  sorry
