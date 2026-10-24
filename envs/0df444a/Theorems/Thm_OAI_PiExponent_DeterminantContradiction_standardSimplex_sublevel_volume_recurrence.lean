-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_recurrence
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_recurrence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:03:20.624359+00:00
-- url     : https://prove2.me/theorems/01eb4695-fd88-4bce-be97-b0794c085fc8
-- title:
--   Dimension recurrence for unit simplex volume
-- statement:
--   The unit simplex volume in dimension `m + 1` is its dimension-`m` volume divided by `m + 1`, by slicing on one coordinate and integrating the scaled slice volumes.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_recurrence (m : Nat) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i : Fin (m + 1), 0 ≤ x i) ∧
      ∑ i : Fin (m + 1), x i ≤ 1}).toReal =
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ 1}).toReal / (m + 1 : Real) := by sorry
