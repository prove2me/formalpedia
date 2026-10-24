-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_factorial
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:09:10.332598+00:00
-- url     : https://prove2.me/theorems/2daf49bf-6198-4ebd-a529-f9d643a0b70d
-- title:
--   Standard simplex volume formula
-- statement:
--   For every natural dimension `n`, the volume of the simplex of nonnegative coordinates with sum at most one is `1 / n!`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_factorial (n : Nat) :
    (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal = 1 / (Nat.factorial n : Real) := by sorry
