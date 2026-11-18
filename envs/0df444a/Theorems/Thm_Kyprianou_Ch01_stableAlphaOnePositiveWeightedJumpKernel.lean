-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveWeightedJumpKernel
-- name    : Kyprianou.Ch01.stableAlphaOnePositiveWeightedJumpKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:44:53.93221+00:00
-- url     : https://prove2.me/theorems/e11446cf-797f-4da9-8688-47dea2da29dd
-- title:
--   Density-weighted compensated jump integrand equals the positive stable alpha-one source kernel
-- statement:
--   For positive r and arbitrary real c and xi, the compensated jump integrand multiplied by the real stable Lévy density c r^(−2) equals minus c times Kyprianou’s complex compensated kernel at frequency xi. This exact pointwise identity bridges LeanLevy’s integrand to the measure-density form needed for the source two-sided stable Lévy characteristic exponent.
-- source:
--   Kyprianou (2006), Chapter 1, Lévy–Khintchine sign convention and stable alpha-one equation (1.8).

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOnePositiveLevyCompensatorBridge
open ProbabilityTheory MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOnePositiveWeightedJumpKernel
    (c xi r : ℝ) (hr : 0 < r) :
    (c * r ^ (-2 : ℝ)) • ProbabilityTheory.levyCompensatedIntegrand xi r =
      -(c : ℂ) * ((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
        Complex.I * (((xi * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
  sorry
