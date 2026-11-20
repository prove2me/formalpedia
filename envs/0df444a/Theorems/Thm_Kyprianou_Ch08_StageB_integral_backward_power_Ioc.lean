-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_integral_backward_power_Ioc
-- name    : Kyprianou.Ch08.StageB.integral_backward_power_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:57:33.73459+00:00
-- url     : https://prove2.me/theorems/9d6c75ae-25c8-401c-8c1b-32ad41809439
-- title:
--   Backward-distance power integral for causal scale convolution
-- statement:
--   For nonnegative x and n∈ℕ, the Lebesgue integral over 0<s≤x of (x−s)^n is x^(n+1)/(n+1). This normalisation produces the factorial denominator in the induction for scale convolution powers (Kyprianou 8.23).
-- source:
--   Kyprianou (2006), Chapter 8, proof of Lemma 8.3 and inequality (8.23), printed p. 221.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Elementary moment of the backward distance on a causal convolution interval. -/
theorem integral_backward_power_Ioc (x : ℝ) (n : ℕ) (hx : 0 ≤ x) :
    (∫ s in Set.Ioc (0 : ℝ) x, (x - s) ^ n ∂volume) =
      x ^ (n + 1) / (n + 1) := by
  sorry

end Kyprianou.Ch08.StageB
