-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_scale
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:52:27.398978+00:00
-- url     : https://prove2.me/theorems/7224017e-201f-45cc-8ea3-d9bd76727610
-- title:
--   Scaling the volume of a simplex sublevel set
-- statement:
--   For positive A, scaling every coordinate of the unit sublevel simplex by A multiplies its volume by A^m. This separates the cutoff dependence from the unit-volume calculation.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_scale {m : Nat} (A : Real) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ A}).toReal = A ^ m *
        (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ 1}).toReal := by sorry
