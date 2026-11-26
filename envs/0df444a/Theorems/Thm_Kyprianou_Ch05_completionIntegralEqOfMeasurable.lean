-- Prove2me | Theorems.Thm_Kyprianou_Ch05_completionIntegralEqOfMeasurable
-- name    : Kyprianou.Ch05.completionIntegralEqOfMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:06:51.65212+00:00
-- url     : https://prove2.me/theorems/598290b3-dd01-4eaa-b458-de404ceac58e
-- title:
--   Completion preserves integrals of real functions measurable in the completion
-- statement:
--   The real codomain has a countably generated sigma algebra. Completed measurability implies original a.e. measurability. The pushforward law and hence integral agree.
-- source:
--   Kyprianou (2006), Chapter 5; completion transport for strong Markov reuse.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.completionIntegralEqOfMeasurable
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (f : Omega → Real)
    (hf : Measurable (fun w : NullMeasurableSpace Omega P => f w)) :
    (∫ w : NullMeasurableSpace Omega P, f w ∂P.completion) =
      ∫ w : Omega, f w ∂P := by
  sorry
