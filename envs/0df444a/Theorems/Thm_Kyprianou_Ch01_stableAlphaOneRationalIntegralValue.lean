-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneRationalIntegralValue
-- name    : Kyprianou.Ch01.stableAlphaOneRationalIntegralValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:15:31.45001+00:00
-- url     : https://prove2.me/theorems/a0611311-9acc-40ec-9d44-a96e4c2b9a81
-- title:
--   Exact π/2 rational integral over the positive half-line for the Laplace cosine kernel
-- statement:
--   The absolutely convergent integral of 1/(1+t²) over positive real t is π/2, by the arctangent primitive. This provides the exact rational integral to which one may reduce the stable alpha-one cosine integral using the positive Laplace representation 1/x²=∫₀∞ t exp(−tx)dt and Tonelli.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable cosine integral; equivalent Laplace representation and rational integral.

import Mathlib
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneRationalIntegralValue :
    (∫ t in Set.Ioi (0 : ℝ), (1 + t ^ 2)⁻¹) = Real.pi / 2 := by
  sorry
