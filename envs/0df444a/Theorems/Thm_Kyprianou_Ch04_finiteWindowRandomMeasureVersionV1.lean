-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteWindowRandomMeasureVersionV1
-- name    : Kyprianou.Ch04.finiteWindowRandomMeasureVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:22:48.478721+00:00
-- url     : https://prove2.me/theorems/33368be4-6476-4a38-a951-1814b051e2ee
-- title:
--   Pointwise finite measurable version of a random measure restriction
-- statement:
--   Patch a random measure restricted to a finite window to zero on the exceptional infinite-mass event; preserve measurable evaluations and almost-sure equality.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteWindowRandomMeasureVersionV1 {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (N : Ω → Measure E) (D : Set E) (hD : MeasurableSet D)
    (hPast : ∀ S : Set E, MeasurableSet S → S ⊆ D → Measurable (fun w => N w S))
    (hFin : ∀ᵐ w ∂P, N w D < ⊤) :
    ∃ R : Ω → Measure E, (∀ w, IsFiniteMeasure (R w)) ∧
      (∀ S : Set E, MeasurableSet S → Measurable (fun w => R w S)) ∧
      ∀ᵐ w ∂P, R w = (N w).restrict D := by
  sorry
end Kyprianou.Ch04
