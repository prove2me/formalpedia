-- Prove2me | Theorems.Thm_Kyprianou_Ch03_boundedStoppingDensityEventV1
-- name    : Kyprianou.Ch03.boundedStoppingDensityEventV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T15:13:24.58665+00:00
-- url     : https://prove2.me/theorems/84e16fd5-2778-4fba-8a93-5f63273515b4
-- title:
--   Bounded optional sampling on a stopped event
-- statement:
--   Bounded optional sampling for a right-continuous integrable martingale, including equality of integrals over a stopped event.
-- source:
--   Kyprianou (2006), Corollary 3.11; faithful support for e939e617-26cc-4e11-98c6-e87492aefbb3

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.boundedStoppingDensityEventV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (Z : NNReal → Omega → ℝ) (hMart : Martingale Z F P)
    (hRight : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => Z u w) (Set.Ici t) t)
    (rho : Omega → NNReal)
    (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal)))
    (n : NNReal) (hBound : ∀ w, rho w ≤ n)
    (B : Set Omega) (hB : MeasurableSet[hStop.measurableSpace] B)
    : Integrable (B.indicator (fun w => Z (rho w) w)) P ∧
      (∫ w, B.indicator (fun v => Z (rho v) v) w ∂P) =
      (∫ w, B.indicator (Z n) w ∂P) := by sorry
