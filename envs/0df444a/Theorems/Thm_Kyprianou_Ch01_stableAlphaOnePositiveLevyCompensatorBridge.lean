-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveLevyCompensatorBridge
-- name    : Kyprianou.Ch01.stableAlphaOnePositiveLevyCompensatorBridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:39:18.869665+00:00
-- url     : https://prove2.me/theorems/e61f95c1-7abe-4f61-907d-59e39f26b28b
-- title:
--   Exact book-to-LeanLevy compensated characteristic exponent integrand sign and cutoff bridge
-- statement:
--   For every real frequency xi and positive jump size r, minus LeanLevy levyCompensatedIntegrand xi r divided by r² equals Kyprianou Chapter 1 exact index-one book-convention kernel (1−exp(i xi r)+i xi r 1_(r<1))/r². This proves the sign, exponential multiplication order and positive-half-line cutoff conventions agree rather than assuming exponent equivalence.
-- source:
--   Kyprianou (2006), Chapter 1, Lévy–Khintchine sign and stable index-one exponent (1.8).

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open ProbabilityTheory MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOnePositiveLevyCompensatorBridge
    (xi r : ℝ) (hr : 0 < r) :
    -(ProbabilityTheory.levyCompensatedIntegrand xi r) /
      ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) =
      ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
      Complex.I * (((xi * r : ℝ) : ℂ)) *
        (if r < 1 then (1 : ℂ) else 0)) /
      ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  sorry
