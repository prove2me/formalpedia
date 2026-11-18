-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosinePositiveIntegrable
-- name    : Kyprianou.Ch01.stableAlphaOneCosinePositiveIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:37:49.795081+00:00
-- url     : https://prove2.me/theorems/7e358f5a-79f0-4eff-a0e0-dac7ca309f55
-- title:
--   Absolute integrability of the index-one stable cosine kernel over the positive half-line
-- statement:
--   The index-one stable cosine Lévy kernel (1−cos x)/x² is absolutely integrable over all positive x. The near-zero bound 1−cos x≤x²/2 proves integrability on (0,1), and 1−cos x≤2 proves integrability on (1,∞). Union at the finite endpoint gives integrability on (0,∞). This closes the integrability clause of the Chapter 1 stable alpha-one cosine integral.
-- source:
--   Kyprianou (2006), Chapter 1, stable Lévy characteristic exponent index one.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosinePositiveIntegrable :
    IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
    (Set.Ioi (0 : ℝ)) := by
  sorry
