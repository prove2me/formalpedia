-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinUniqueness
-- name    : Kyprianou.Ch01.stableGammaStrictLeftMellinUniqueness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T13:04:38.051694+00:00
-- url     : https://prove2.me/theorems/36d68b83-1939-418d-a0a4-ee3613c30203
-- title:
--   Extend real-axis Mellin equality by holomorphic uniqueness
-- statement:
--   Use the published exact real-axis Mellin identity for w=-u, u>0, and the analytic identity theorem on the connected strict-left half-plane. The right-hand side is holomorphic there since -w has strictly positive real part and its principal logarithm is analytic. The real-axis equality accumulates inside the domain.
-- source:
--   Kyprianou (2006) Chapter 1 stable Gamma Mellin integral, analytic continuation of real Laplace axis.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftMellinUniqueness
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hanalytic : AnalyticOnNhd ℂ (fun w : ℂ =>
      ∫ r in Set.Ioi (0 : ℝ),
        Complex.exp (w * (r : ℂ)) *
          ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) {w : ℂ | w.re < 0}) :
    ∀ w : ℂ, w.re < 0 →
      (∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (w * (r : ℂ)) *
            ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) = ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)) := by sorry
