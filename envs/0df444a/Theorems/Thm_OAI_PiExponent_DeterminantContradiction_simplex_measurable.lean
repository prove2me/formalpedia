-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_measurable
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_measurable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:27:03.703769+00:00
-- url     : https://prove2.me/theorems/492ff344-51e9-4eb9-b248-08317352e9cc
-- title:
--   Measurability of the open simplex
-- statement:
--   The simplex defined by finitely many coordinate lower bounds and one strict sum bound is measurable. Prove by expressing it as a finite intersection of preimages of measurable intervals under continuous coordinate and sum maps.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_measurable (m : Nat) (T : Real) :
    MeasurableSet {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by sorry
