-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedRightContinuousMartingaleEventBalance
-- name    : Kyprianou.Ch04.clippedRightContinuousMartingaleEventBalance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:56:42.236099+00:00
-- url     : https://prove2.me/theorems/186bd599-2ebc-5344-b441-c056f4cbb2e1
-- title:
--   clippedRightContinuousMartingaleEventBalance
-- statement:
--   Clipping a right-continuous martingale at a stopping time yields integrable values and equal event integrals at ordered deterministic times.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A bounded-horizon stopped right-continuous martingale has zero event increments. -/
theorem Kyprianou.Ch04.clippedRightContinuousMartingaleEventBalance {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (J : NNReal → Omega → ℝ) (hM : Martingale J F.rightCont P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u => J u w) (Set.Ici t) t)
    (tau : Omega → WithTop NNReal) (ht : IsStoppingTime F.rightCont tau) :
    let C := fun (t : NNReal) w => J ((min (tau w) (t : WithTop NNReal)).untopD t) w
    (∀ t, Integrable (C t) P) ∧
      ∀ s t, s ≤ t → ∀ A : Set Omega, MeasurableSet[F.rightCont s] A →
        (∫ w in A, C s w ∂P) = ∫ w in A, C t w ∂P := by
  sorry
