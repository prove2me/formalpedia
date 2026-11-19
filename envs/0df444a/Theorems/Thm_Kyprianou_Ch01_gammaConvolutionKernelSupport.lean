-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaConvolutionKernelSupport
-- name    : Kyprianou.Ch01.gammaConvolutionKernelSupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:11:39.12098+00:00
-- url     : https://prove2.me/theorems/18df5649-d394-467f-82a0-84de65faf761
-- title:
--   Gamma convolution integrand has a polynomial kernel on the exact support interval
-- statement:
--   For z≥0, the product of rate-beta Gamma(n+1) and Gamma(1) density factors at x and z-x is zero outside [0,z], and inside equals beta^(n+2)*exp(-beta*z)*x^n/n!. This pointwise support identity is the algebraic part of the independent gamma convolution calculation.
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), solution pp.304–305

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_levy_foundations_arrivalGammaDensity
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaConvolutionKernelSupport
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (x : ℝ) :
    LevyFoundations.arrivalGammaDensity beta n x *
      LevyFoundations.arrivalGammaDensity beta 0 (z - x) =
    (Set.Icc (0 : ℝ) z).indicator
      (fun y : ℝ => ENNReal.ofReal
        ((beta ^ (n + 2) * Real.exp (-(beta * z)) /
          (n.factorial : ℝ)) * y ^ n)) x := by
  sorry
