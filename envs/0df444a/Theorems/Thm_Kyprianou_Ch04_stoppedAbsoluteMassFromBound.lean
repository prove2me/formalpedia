-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stoppedAbsoluteMassFromBound
-- name    : Kyprianou.Ch04.stoppedAbsoluteMassFromBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:39:00.407964+00:00
-- url     : https://prove2.me/theorems/9812e73b-154f-553e-aaec-d5d1d0765664
-- title:
--   stoppedAbsoluteMassFromBound
-- statement:
--   A uniform bound on the stopped positive-time mark integral yields finite expected mass.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A uniform bound on the stopped positive-time mark integral yields finite expected mass. -/
theorem Kyprianou.Ch04.stoppedAbsoluteMassFromBound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (nu : Measure ℝ) (k : ℝ → ℝ → Ω → ℝ) (tau : Ω → WithTop NNReal)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hb : ∀ᵐ w ∂P, ∀ s : ℝ, 0 < s → (s.toNNReal : WithTop NNReal) ≤ tau w →
      (∫⁻ x, ENNReal.ofReal |k s x w| ∂nu) ≤ B) (t : NNReal) :
    (∫⁻ w, ∫⁻ s in Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
      ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0|
      ∂nu ∂volume ∂P) < ⊤ := by
  sorry
