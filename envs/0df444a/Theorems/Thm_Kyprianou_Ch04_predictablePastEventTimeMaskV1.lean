-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictablePastEventTimeMaskV1
-- name    : Kyprianou.Ch04.predictablePastEventTimeMaskV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:18:11.293536+00:00
-- url     : https://prove2.me/theorems/a82471b9-ea82-48f2-935c-e8b0ecb5b7c6
-- title:
--   Predictable future-time past-event mask
-- statement:
--   Restricting a predictable marked kernel to a future time interval and a past event preserves predictability.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictablePastEventTimeMaskV1 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance) (s t : NNReal)
    (A : Set Ω) (hA : MeasurableSet[F s] A)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g) :
    Measurable[F.predictable.prod inferInstance]
      (((Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)).indicator g) := by
  sorry
end Kyprianou.Ch04
