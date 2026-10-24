-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_toReal
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_toReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:48:55.204502+00:00
-- url     : https://prove2.me/theorems/b9ccf56c-4ab4-401a-9e57-33ca3b22d9e6
-- title:
--   Volume of a standard simplex sublevel set
-- statement:
--   For a positive cutoff, the volume of the nonnegative simplex with coordinate sum at most the cutoff is the cutoff raised to the dimension divided by the dimension factorial.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_toReal {m : Nat} (A : Real) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ A}).toReal = A ^ m / (m.factorial : Real) := by sorry
