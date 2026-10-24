-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_explicitBounds_volume_succ_slice
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_volume_succ_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:57:15.562547+00:00
-- url     : https://prove2.me/theorems/4902366c-e584-47e6-abd3-2996b1b2243e
-- title:
--   Explicit-bound simplex volume by coordinate slices
-- statement:
--   The volume in dimension `m + 1` is the integral of the volumes of its coordinate slices. Decompose coordinates as `ℝ × (Fin m → ℝ)`, use product-measure slicing, and identify the fiber at `t` with the simplex whose cutoff is `A - t`. For `A = 0`, both sides vanish; nonnegative `A` ensures the displayed interval and slices have the stated bounds. This removes the main geometric measure argument from the induction.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_volume_succ_slice (m : Nat) (A : Real) (hA : 0 ≤ A) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A}).toReal =
      ∫ t in Set.Icc (0 : Real) A,
        (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ A - t}).toReal := by sorry
