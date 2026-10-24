-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:35:47.432307+00:00
-- url     : https://prove2.me/theorems/bdb6e2a9-317a-4b76-ab7d-106fcc4ded2e
-- title:
--   Coordinate simplex volume recurrence
-- statement:
--   The volume in dimension n+1 is the volume in dimension n divided by n+1. Slice by one coordinate t; for 0 ≤ t ≤ 1 the remaining section is a copy of the n-dimensional simplex scaled by 1−t, and integrating its scaled volume gives the stated recurrence.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_succ (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i : Fin (n + 1), 0 ≤ x i) ∧
      ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
        ∑ i : Fin n, x i ≤ 1}).toReal / (n + 1 : Real) := by sorry
