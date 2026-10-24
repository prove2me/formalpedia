-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_measurable_box_finite_volume
-- name    : OAI.PiExponent.DeterminantContradiction.measurable_box_finite_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:26:05.397081+00:00
-- url     : https://prove2.me/theorems/c7b913c9-003c-4a8d-8df4-4c91951e6a77
-- title:
--   Finite volume of a measurable subset of a coordinate box
-- statement:
--   A measurable subset of the finite-dimensional coordinate box [0,A]^(m+1) has finite volume.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.measurable_box_finite_volume (m : Nat) (A : Real) (hA : 0 ≤ A) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) (hbox : s ⊆ {x | ∀ i, x i ∈ Set.Icc (0 : Real) A}) : MeasureTheory.volume s ≠ ⊤ := by sorry
