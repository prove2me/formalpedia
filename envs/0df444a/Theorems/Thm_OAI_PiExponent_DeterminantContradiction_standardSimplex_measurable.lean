-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_measurable
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:14:24.408539+00:00
-- url     : https://prove2.me/theorems/b6c2d16e-d7c9-4ad0-adbb-ea0b6b2a5972
-- title:
--   Measurability of the standard simplex
-- statement:
--   The standard simplex is closed, hence measurable; it is an intersection of finitely many closed coordinate half-spaces and one closed sum half-space.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable (n : Nat) :
    MeasurableSet {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} := by sorry
