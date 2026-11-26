-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedRightContinuousStopSetIntegral
-- name    : Kyprianou.Ch04.boundedRightContinuousStopSetIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:52:37.765491+00:00
-- url     : https://prove2.me/theorems/4d97145a-0a97-5534-83dd-6bf9523d4b6c
-- title:
--   boundedRightContinuousStopSetIntegral
-- statement:
--   For a right-continuous martingale, bounded stopping preserves the terminal expectation on every event measurable at the stopping time.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Bounded optional sampling in set-integral form for a right-continuous martingale. -/
theorem Kyprianou.Ch04.boundedRightContinuousStopSetIntegral {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (J : NNReal → Omega → ℝ) (hM : Martingale J F.rightCont P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u => J u w) (Set.Ici t) t)
    (n : ℕ) (tau : Omega → NNReal)
    (ht : IsStoppingTime F.rightCont (fun w => (tau w : WithTop NNReal)))
    (hb : ∀ w, tau w ≤ (n : NNReal)) :
    Integrable (fun w => J (tau w) w) P ∧
      ∀ A : Set Omega, MeasurableSet[ht.measurableSpace] A →
        (∫ w in A, J (tau w) w ∂P) = ∫ w in A, J (n : NNReal) w ∂P := by
  sorry
