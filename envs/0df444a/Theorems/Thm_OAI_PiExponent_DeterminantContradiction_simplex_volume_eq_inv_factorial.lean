-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_eq_inv_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_eq_inv_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:21:36.933116+00:00
-- url     : https://prove2.me/theorems/931dbb03-d175-42b4-b264-c5028ce4e64d
-- title:
--   Volume of the standard coordinate simplex
-- statement:
--   For every natural number n, the volume of the nonnegative coordinate simplex in Fin n with coordinate sum at most one is the reciprocal of n factorial.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_eq_inv_factorial (n : Nat) :
    (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal = 1 / (Nat.factorial n : Real) := by sorry
