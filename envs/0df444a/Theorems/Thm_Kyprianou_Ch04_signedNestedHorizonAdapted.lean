-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedNestedHorizonAdapted
-- name    : Kyprianou.Ch04.signedNestedHorizonAdapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:15:59.548207+00:00
-- url     : https://prove2.me/theorems/63944f6d-b472-4770-b399-e77dca3e43b8
-- title:
--   signedNestedHorizonAdapted
-- statement:
--   Exact signed nested compensator measurability follows from joint past-cutoff measurability.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact nested signed compensator measurability follows from the past cutoff. -/
theorem Kyprianou.Ch04.signedNestedHorizonAdapted {Omega : Type} [MeasurableSpace Omega]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (k : ℝ → ℝ → Omega → ℝ) (t : NNReal)
    (hm : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) :
    StronglyMeasurable[F t] (fun w => ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫ x, k s x w ∂nu ∂volume) := by
  sorry
