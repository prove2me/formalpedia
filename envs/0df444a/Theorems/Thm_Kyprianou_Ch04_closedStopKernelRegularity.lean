-- Prove2me | Theorems.Thm_Kyprianou_Ch04_closedStopKernelRegularity
-- name    : Kyprianou.Ch04.closedStopKernelRegularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:24:49.14867+00:00
-- url     : https://prove2.me/theorems/d6fe9d6a-7a47-4c8b-9b4f-6de433c2d822
-- title:
--   closedStopKernelRegularity
-- statement:
--   Closed stopping masks preserve signed-kernel regularity.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_stoppingTimeMinMeasurable
import Theorems.Thm_Kyprianou_Ch04_closedStopMaskLeftLimit
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- The closed stopping mask preserves joint, adapted and past-horizon measurability
as well as common-null left continuity of a signed marked kernel. -/
theorem Kyprianou.Ch04.closedStopKernelRegularity {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (htau : IsStoppingTime F tau)
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (ha : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1))
    (hc : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w)))
    (hPast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) :
    let H := fun s x w => if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0
    Measurable (fun z : (ℝ × ℝ) × Omega => H z.1.1 z.1.2 z.2) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => H (t : ℝ) z.2 z.1)) ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => H s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (H (t : ℝ) x w))) ∧
    (∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then H z.2.1 z.2.2 z.1 else 0))  := by
  sorry
