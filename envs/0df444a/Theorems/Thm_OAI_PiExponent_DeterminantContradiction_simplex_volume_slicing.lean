-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_slicing
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:28:39.726796+00:00
-- url     : https://prove2.me/theorems/5f575aa4-fe69-4b04-b543-52fc9f34f103
-- title:
--   Coordinate simplex volume recurrence by slicing
-- statement:
--   The volume of the coordinate simplex in dimension n+1 is its dimension-n volume divided by n+1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i : Fin (n + 1), 0 ≤ x i) ∧
      ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
    ((MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal) / ((n + 1 : Nat) : Real) := by sorry
