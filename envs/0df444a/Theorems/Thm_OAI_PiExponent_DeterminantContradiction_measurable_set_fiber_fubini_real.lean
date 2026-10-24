-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_measurable_set_fiber_fubini_real
-- name    : OAI.PiExponent.DeterminantContradiction.measurable_set_fiber_fubini_real
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:25:52.304706+00:00
-- url     : https://prove2.me/theorems/5611bdcb-ea82-4b23-84f9-99bef9d9fac4
-- title:
--   Whole-line real-valued Fubini formula for coordinate fibers
-- statement:
--   For a measurable set of finite volume in Fin (m+1)-dimensional real coordinate space, the real-valued volumes of its fibers are integrable over the whole first-coordinate line, and their integral equals the set’s volume.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.measurable_set_fiber_fubini_real (m : Nat) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) (hfinite : MeasureTheory.volume s ≠ ⊤) : (MeasureTheory.Integrable (fun t : Real => (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈ s}).toReal) MeasureTheory.volume) ∧ (MeasureTheory.integral MeasureTheory.volume (fun t : Real => (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈ s}).toReal) = (MeasureTheory.volume s).toReal) := by sorry
