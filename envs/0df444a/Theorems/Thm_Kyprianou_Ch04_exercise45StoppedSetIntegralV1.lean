-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45StoppedSetIntegralV1
-- name    : Kyprianou.Ch04.exercise45StoppedSetIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:36:10.127541+00:00
-- url     : https://prove2.me/theorems/d7e78a03-a0f8-46cc-a213-96e0150579c6
-- title:
--   Set-integral equalities for the stopped martingale
-- statement:
--   Right-continuous martingales have integrable clipped values and equal integrals over earlier measurable events.
-- source:
--   Kyprianou Exercise 4.5

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45StoppedSetIntegralV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration NNReal inferInstance) (hRC : F.IsRightContinuous)
    (J : NNReal → Ω → ℝ) (hM : Martingale J F P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (τ : Ω → NNReal) (ht : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    (∀ i, Integrable (fun w => J (min i (τ w)) w) P) ∧
    (∀ s t : NNReal, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      (∫ w in A, J (min s (τ w)) w ∂P) = ∫ w in A, J (min t (τ w)) w ∂P) := by
  sorry
end Kyprianou.Ch04
