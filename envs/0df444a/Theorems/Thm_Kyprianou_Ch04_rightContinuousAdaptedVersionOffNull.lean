-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousAdaptedVersionOffNull
-- name    : Kyprianou.Ch04.rightContinuousAdaptedVersionOffNull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:54:21.22412+00:00
-- url     : https://prove2.me/theorems/1f159564-1102-546b-835c-02e5c29f823c
-- title:
--   rightContinuousAdaptedVersionOffNull
-- statement:
--   A common-null right-continuous adapted version with exact agreement outside its null set.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A common-null right-continuous adapted version with exact agreement outside its null set. -/
theorem Kyprianou.Ch04.rightContinuousAdaptedVersionOffNull {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hJ : StronglyAdapted F J)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t) :
    ∃ (N : Set Ω) (K : NNReal → Ω → ℝ), MeasurableSet N ∧ P N = 0 ∧
      (∀ t, Measurable[F t] (K t)) ∧
      (∀ w t, ContinuousWithinAt (fun u => K u w) (Ici t) t) ∧
      ∀ w, w ∉ N → ∀ t, K t w = J t w := by
  sorry
