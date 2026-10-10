-- Prove2me | Theorems.Thm_MeasureTheory_eqOn_of_le_setAverage
-- name    : MeasureTheory.eqOn_of_le_setAverage
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T15:53:48.863257+00:00
-- url     : https://prove2.me/theorems/78096bf6-3003-47bd-9cfc-c3e2667d9c53
-- title:
--   Rigidity at an upper bound equal to the average
-- statement:
--   Let μ be a measure that assigns positive measure to every nonempty open set. Let s be an open set of finite measure and let f be a continuous, integrable real function on s. If f(x) is at most its normalized average over s for every x in s, then f is identically equal to that average on s. This includes the empty set. The conclusion follows because the nonnegative continuous deficit from the average has integral zero.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 26, proof of Theorem 2.13: equality in the mean-value bound forces constancy on a ball. This theorem isolates that measure-theoretic argument and generalizes it to finite-measure open sets and measures positive on nonempty open sets.

import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false

theorem MeasureTheory.eqOn_of_le_setAverage {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsOpenPosMeasure μ]
    {s : Set X} {f : X → ℝ} (hs : IsOpen s) (hfinite : μ s ≠ ∞)
    (hc : ContinuousOn f s) (hi : IntegrableOn f s μ)
    (hle : ∀ x ∈ s, f x ≤ ⨍ y in s, f y ∂μ) :
    EqOn f (fun _ => ⨍ y in s, f y ∂μ) s  := by sorry
