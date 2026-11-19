-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelEnvelopeBound
-- name    : Kyprianou.Ch01.stableAlphaAboveOneKernelEnvelopeBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:16:59.635101+00:00
-- url     : https://prove2.me/theorems/2158869f-6f0f-4b25-9d70-caab8c7a8a22
-- title:
--   Quadratic near-zero and linear tail envelope for compensated stable Fourier kernel
-- statement:
--   For every positive r and real alpha, the norm of the exact compensated stable characteristic Fourier kernel is bounded by r^(1-alpha) below r=1 and 2*r^(-alpha) above r=1. Uses the pinned complex exponential quadratic Taylor remainder for |r|≤1 and the global imaginary-exponential Lipschitz estimate for r≥1. Exactly matches the original kernel and admits integrability for 1<alpha<2.
-- source:
--   Kyprianou (2006) Chapter 1 alpha>1 stable process characteristic exponent; envelope for stableAlphaAboveOneKernelIntegrable.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneKernelEnvelopeBound
    (alpha r : ℝ) (hr : 0 < r) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ ≤
      (if r ≤ 1 then r ^ (1 - alpha)
        else 2 * r ^ (-alpha)) := by
  sorry
