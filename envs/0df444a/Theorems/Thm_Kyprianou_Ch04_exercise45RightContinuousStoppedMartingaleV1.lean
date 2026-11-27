-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45RightContinuousStoppedMartingaleV1
-- name    : Kyprianou.Ch04.exercise45RightContinuousStoppedMartingaleV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:31:08.197137+00:00
-- url     : https://prove2.me/theorems/cc64fa5c-e7e1-483b-acc0-f970a8ffe1cd
-- title:
--   Finite stopping preserves a right-continuous martingale in a complete right-continuous filtration
-- statement:
--   A real martingale with almost-sure right-continuous paths remains a martingale when stopped at a finite stopping clock in a complete right-continuous filtration.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), bounded optional sampling.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Stopping a right-continuous martingale at a finite clock preserves its martingale property. -/
theorem Kyprianou.Ch04.exercise45RightContinuousStoppedMartingaleV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration NNReal inferInstance) (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hM : Martingale J F P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (τ : Ω → NNReal) (ht : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    Martingale (fun t w => J (min t (τ w)) w) F P := by
  sorry
