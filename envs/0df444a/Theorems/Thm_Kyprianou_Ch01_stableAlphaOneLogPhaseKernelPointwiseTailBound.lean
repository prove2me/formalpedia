-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseKernelPointwiseTailBound
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseKernelPointwiseTailBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:46:22.841578+00:00
-- url     : https://prove2.me/theorems/6931bbd7-4665-4ef4-a0fe-715bf5199dd5
-- title:
--   Exact pointwise 1/r² bound for the compensated alpha-one stable complex kernel
-- statement:
--   For z>0 and r>0, the exact source compensated complex alpha-one stable Lévy kernel has norm bounded by (2+z)/r². The complex exponential contributes at most two, while the original cutoff makes the linear compensation vanish for r≥1 and bounded by z for r<1.
-- source:
--   Kyprianou (2006), Chapter 1, logarithmic index-one stable Lévy exponent.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseKernelPointwiseTailBound
    (z r : ℝ) (hz : 0 < z) (hrpos : 0 < r) :
    ‖((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)‖ ≤ (2 + z) * r ^ (-2 : ℝ) := by
  sorry
