-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_compact
-- name    : OAI.PiExponent.DeterminantContradiction.standard_simplex_compact
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:53:13.168251+00:00
-- url     : https://prove2.me/theorems/338c62dd-3627-4b6a-94fc-ea45875887bb
-- title:
--   Compactness of the ordinary simplex
-- statement:
--   The nonnegative simplex with coordinate sum at most a positive bound is compact.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standard_simplex_compact {m : Nat} (A : Real) (hA : 0 < A) :
    IsCompact {y : Fin m → Real | (∀ i : Fin m, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A} := by sorry
