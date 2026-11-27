-- Prove2me | Theorems.Thm_Kyprianou_Ch04_localisationOuterEventLimitV1
-- name    : Kyprianou.Ch04.localisationOuterEventLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:59:56.963209+00:00
-- url     : https://prove2.me/theorems/178b45bd-ed36-4d91-9887-9c7fbe075330
-- title:
--   Outer probability localisation with a vanishing exceptional event
-- statement:
--   If each error event is contained in a vanishing outer probability exceptional event union an approximation error converging to zero for each fixed localisation index, the original outer probability converges to zero.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

/-- Local error estimates with vanishing exceptional outer probability imply convergence. -/
theorem Kyprianou.Ch04.localisationOuterEventLimitV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Set Ω) (A : ℕ → ℕ → Set Ω) (E : ℕ → Set Ω)
    (hB : Tendsto (fun n => (P (B n)).toReal) atTop (nhds 0))
    (hA : ∀ n, Tendsto (fun j => (P (A n j)).toReal) atTop (nhds 0))
    (hSub : ∀ n j, E j ⊆ B n ∪ A n j) :
    Tendsto (fun j => (P (E j)).toReal) atTop (nhds 0) := by
  sorry
