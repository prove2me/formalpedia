-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RationalClockMeasurableV3
-- name    : Kyprianou.Ch04.exercise49RationalClockMeasurableV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:39:40.32821+00:00
-- url     : https://prove2.me/theorems/39256f45-cbdc-43bf-b063-b3f149c2c7d1
-- title:
--   The countably sampled real strict negative passage clock is measurable
-- statement:
--   The countably sampled real strict negative passage clock is measurable
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RationalClockMeasurableV3
    {Ω : Type} [MeasurableSpace Ω] (Z : NNReal → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) :
    Measurable (fun ω : Ω => ⨅ q : ℚ,
      if 0 < (q : ℝ) ∧ Z (Real.toNNReal q) ω < 0 then
        (↑(Real.toNNReal q) : WithTop NNReal) else ⊤) := by
  sorry
