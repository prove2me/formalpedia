-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_slice
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:44:48.803816+00:00
-- url     : https://prove2.me/theorems/1ba28f6c-2bd1-4ee5-9185-960f2bd87ffc
-- title:
--   Coordinate simplex volume by slicing
-- statement:
--   The volume of the (n+1)-dimensional coordinate simplex is the integral from 0 to 1 of the volumes of its n-dimensional sections, whose coordinate sum is at most 1−t.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_slice (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i : Fin (n + 1), 0 ≤ x i) ∧
      ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      ∫ t in (0 : Real)..1, (MeasureTheory.volume {y : Fin n → Real |
        (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ 1 - t}).toReal := by sorry
