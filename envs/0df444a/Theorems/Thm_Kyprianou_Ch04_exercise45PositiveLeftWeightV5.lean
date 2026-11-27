-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PositiveLeftWeightV5
-- name    : Kyprianou.Ch04.exercise45PositiveLeftWeightV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:41:50.950689+00:00
-- url     : https://prove2.me/theorems/98dfcd4e-6416-4368-b435-54f685c89135
-- title:
--   Positive left-limit weight coordinates are almost surely measurable
-- statement:
--   Positive left-limit weight coordinates are almost surely measurable
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45PositiveLeftWeightV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y L : NNReal → Ω → ℝ) (f : ℝ → ℝ → ℝ)
    (hm : ∀ t, AEMeasurable (Y t) P)
    (hl : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hf : ∀ t : NNReal, Continuous (f (t : ℝ))) :
    ∀ t : NNReal, AEMeasurable (fun w => if t = 0 then 0 else f (t : ℝ) (L t w)) P := by
  sorry
