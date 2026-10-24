-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_unit
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_unit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:52:48.555736+00:00
-- url     : https://prove2.me/theorems/f0bc27af-043f-4804-b5a3-5018c473578f
-- title:
--   Volume of the unit simplex sublevel set
-- statement:
--   The nonnegative simplex with coordinate sum at most one in Fin m-dimensional real space has volume 1/m!. This is the core calculation, proved by induction and Fubini.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_unit {m : Nat} :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ 1}).toReal = 1 / (m.factorial : Real) := by sorry
