-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseTailIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseTailIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:37:56.632197+00:00
-- url     : https://prove2.me/theorems/c7fac915-47f2-4f32-946c-6c5ab4991420
-- title:
--   Bochner integrability of the full compensated complex stable alpha-one tail
-- statement:
--   For any real frequency z, the exact complex compensated stable index-one kernel is absolutely integrable over r>1. The original small-jump compensation vanishes there; the numerator norm |1−exp(i z r)| is at most two, and r^(−2) has integrable positive-half-line tail.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy exponent.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseTailIntegrable
    (z : ℝ) :
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioi (1 : ℝ)) := by
  sorry
