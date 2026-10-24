-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_measurable_box_fubini_real
-- name    : OAI.PiExponent.DeterminantContradiction.measurable_box_fubini_real
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:13:58.312271+00:00
-- url     : https://prove2.me/theorems/a6934c97-17e7-4845-adf0-b2f3fe0bf02f
-- title:
--   Real-valued Fubini formula for measurable subsets of a box
-- statement:
--   For a measurable subset of a finite-dimensional coordinate box, its volume is the integral over the first coordinate of the volumes of its coordinate fibers. The box hypothesis gives finite volume and confines the slicing coordinate to the displayed interval.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.measurable_box_fubini_real (m : Nat) (A : Real) (hA : 0 ≤ A) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) (hbox : s ⊆ {x | ∀ i, x i ∈ Set.Icc (0 : Real) A}) :
    (MeasureTheory.volume s).toReal =
      ∫ t in Set.Icc (0 : Real) A,
        (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈ s}).toReal := by sorry
