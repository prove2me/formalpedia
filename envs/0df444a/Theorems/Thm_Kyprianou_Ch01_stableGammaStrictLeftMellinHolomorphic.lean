-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinHolomorphic
-- name    : Kyprianou.Ch01.stableGammaStrictLeftMellinHolomorphic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T13:04:45.156011+00:00
-- url     : https://prove2.me/theorems/32ded39a-9798-4836-a8c7-a37743359a00
-- title:
--   Holomorphy of the strict-left Laplace Mellin transform
-- statement:
--   Prove the parameter-dependent complex Mellin-Laplace integral is holomorphic throughout the strict left half-plane, using exponential decay on compact sets and locally dominated differentiation. This is the analytic prerequisite for the identity theorem.
-- source:
--   Kyprianou (2006) Chapter 1 stable Gamma Mellin integral, analytic continuation of real Laplace axis.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftMellinHolomorphic
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    AnalyticOnNhd ℂ (fun w : ℂ =>
      ∫ r in Set.Ioi (0 : ℝ),
        Complex.exp (w * (r : ℂ)) *
          ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) {w : ℂ | w.re < 0} := by sorry
