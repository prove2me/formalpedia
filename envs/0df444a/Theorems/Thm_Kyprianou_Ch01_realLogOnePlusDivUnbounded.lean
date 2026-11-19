-- Prove2me | Theorems.Thm_Kyprianou_Ch01_realLogOnePlusDivUnbounded
-- name    : Kyprianou.Ch01.realLogOnePlusDivUnbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:00:35.104567+00:00
-- url     : https://prove2.me/theorems/dfb6e9b6-71e2-43fa-8470-84524f1ce769
-- title:
--   Explicit nonnegative time with harmonic logarithm divided by positive constant arbitrarily large
-- statement:
--   The logarithmic harmonic primitive log(1+s)/C is unbounded over s≥0, for any fixed C>0. An explicit witness can be constructed using the exponential map at C*t+1 and its strict positivity. This forms the final elementary real-analysis step of the inverse-speed clock divergence proof.
-- source:
--   Real.log_exp and the monotonicity of the real logarithm. Kyprianou (2006) Chapter 1 §1.3.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Real
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.realLogOnePlusDivUnbounded
    (C : ℝ) (hC : 0 < C) (t : ℝ≥0) :
    ∃ s : ℝ≥0,
      (t : ℝ) < Real.log (1 + (s : ℝ)) / C := by
  sorry
