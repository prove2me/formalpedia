-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_measurable_subset_box
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable_subset_box
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:14:08.578984+00:00
-- url     : https://prove2.me/theorems/9b5b2598-7e5d-421e-aec3-47f88e40be62
-- title:
--   Simplex measurability and coordinate box bound
-- statement:
--   The nonnegative-coordinate simplex cut out by the sum bound is measurable and lies in the coordinate box [0,A]^(m+1). Closedness gives measurability; nonnegativity and the sum bound imply each coordinate is at most A.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable_subset_box (m : Nat) (A : Real) (hA : 0 ≤ A) :
    MeasurableSet {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A} ∧
      {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A} ⊆
        {x | ∀ i, x i ∈ Set.Icc (0 : Real) A} := by sorry
