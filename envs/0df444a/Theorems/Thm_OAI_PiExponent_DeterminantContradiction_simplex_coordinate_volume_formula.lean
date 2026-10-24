-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_formula
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:31:33.637511+00:00
-- url     : https://prove2.me/theorems/42a5a03a-a2be-4646-848e-1d6d5820c7e7
-- title:
--   Coordinate simplex volume in factorial form
-- statement:
--   For every natural dimension n, the coordinate simplex of nonnegative coordinates whose sum is at most 1 has volume 1/n!.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula (n : Nat) :
    (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal = 1 / (Nat.factorial n : Real) := by sorry
