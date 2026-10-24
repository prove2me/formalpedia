-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_for_explicit_bounds
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_for_explicit_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:45:20.853667+00:00
-- url     : https://prove2.me/theorems/97aa5483-755a-4c46-a130-27407cd07fb7
-- title:
--   Volume of the standard simplex
-- statement:
--   For any nonnegative cutoff A, the standard simplex in m real coordinates has volume A^m/m!, including the zero-dimensional case.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_for_explicit_bounds {m : Nat} (A : Real) (hA : 0 ≤ A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ A}).toReal =
      A ^ m / ((Nat.factorial m : Nat) : Real) := by sorry
