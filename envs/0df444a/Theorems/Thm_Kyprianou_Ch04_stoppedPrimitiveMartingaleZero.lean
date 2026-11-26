-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stoppedPrimitiveMartingaleZero
-- name    : Kyprianou.Ch04.stoppedPrimitiveMartingaleZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:20:39.200304+00:00
-- url     : https://prove2.me/theorems/3fee363f-dbbe-5a38-b4a7-620b7c5b722c
-- title:
--   stoppedPrimitiveMartingaleZero
-- statement:
--   A primitive of a bounded time density which is a martingale vanishes.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- A primitive of a bounded time density which is a martingale vanishes. -/
theorem Kyprianou.Ch04.stoppedPrimitiveMartingaleZero {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (g : ℝ → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ w ∂P,
      (∀ t : NNReal, IntegrableOn (fun r => g r w) (Icc (0 : ℝ) (t : ℝ)) volume) ∧
      (∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)), ‖g r w‖ ≤ C))
    (hM : Martingale (fun (t : NNReal) w =>
      ∫ r in Icc (0 : ℝ) (t : ℝ), g r w ∂volume) F P) :
    ∀ t : NNReal, ∀ᵐ w ∂P, (∫ r in Icc (0 : ℝ) (t : ℝ), g r w ∂volume) = 0 := by
  sorry
