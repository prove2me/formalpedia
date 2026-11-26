-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedRightContinuousAdapted
-- name    : Kyprianou.Ch04.clippedRightContinuousAdapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:48:39.59037+00:00
-- url     : https://prove2.me/theorems/fe4a5435-e758-5160-9501-c97e825cd40d
-- title:
--   clippedRightContinuousAdapted
-- statement:
--   Clipping an adapted right-continuous path at a stopping time preserves adaptedness.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Clipping an adapted right-continuous path at a stopping time preserves adaptedness. -/
theorem Kyprianou.Ch04.clippedRightContinuousAdapted {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hJ : StronglyAdapted F J)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (tau : Ω → WithTop NNReal) (ht : IsStoppingTime F tau) :
    StronglyAdapted F (fun (t : NNReal) w =>
      J ((min (tau w) (t : WithTop NNReal)).untopD t) w) := by
  sorry
