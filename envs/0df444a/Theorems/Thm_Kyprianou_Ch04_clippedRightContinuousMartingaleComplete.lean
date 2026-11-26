-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedRightContinuousMartingaleComplete
-- name    : Kyprianou.Ch04.clippedRightContinuousMartingaleComplete
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:43:58.187876+00:00
-- url     : https://prove2.me/theorems/74788e74-3a33-529a-a6f4-7c5e34cc1f83
-- title:
--   clippedRightContinuousMartingaleComplete
-- statement:
--   Bounded clipping preserves a right-continuous martingale in a usual filtration.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Bounded clipping preserves a right-continuous martingale in a usual filtration. -/
theorem Kyprianou.Ch04.clippedRightContinuousMartingaleComplete {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hM : Martingale J F P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (tau : Ω → WithTop NNReal) (ht : IsStoppingTime F tau) :
    Martingale (fun (t : NNReal) w =>
      J ((min (tau w) (t : WithTop NNReal)).untopD t) w) F P := by
  sorry
