-- Prove2me | Theorems.Thm_Kyprianou_Ch05_completionMapEqOfAEMeasurable
-- name    : Kyprianou.Ch05.completionMapEqOfAEMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:06:55.443847+00:00
-- url     : https://prove2.me/theorems/4e602865-7156-43a3-a46a-16ace804527c
-- title:
--   Completion preserves laws of almost-everywhere measurable functions
-- statement:
--   Use map_apply on the completed domain, where the originally a.e. measurable function is measurable. Completion has exactly the same outer measure.
-- source:
--   Kyprianou (2006), Chapter 5; completion transport for strong Markov reuse.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.completionMapEqOfAEMeasurable
    {Omega B : Type} [MeasurableSpace Omega] [MeasurableSpace B]
    (P : Measure Omega) (f : Omega → B) (hf : AEMeasurable f P) :
    Measure.map (fun w : NullMeasurableSpace Omega P => f w) P.completion =
      Measure.map f P := by
  sorry
