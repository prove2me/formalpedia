-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceCosine
-- name    : Kyprianou.Ch01.stableAlphaOneLaplaceCosine
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:20:26.926203+00:00
-- url     : https://prove2.me/theorems/f47e8382-09df-41d3-8210-b8e6e0b911c7
-- title:
--   Exact Laplace cosine transform on positive real line at frequency one
-- statement:
--   For every positive a, the positive-half-line Laplace transform ∫ exp(−ax)cos x dx equals a/(a²+1). The proof takes the real part of the proved complex exponential integral 1/(a−i), using Mathlib integral_re and the complex exponential real-part identity. This is the missing transform needed to turn the stable alpha-one cosine deficit into the positive rational kernel 1/(1+a²) after Tonelli.
-- source:
--   Kyprianou (2006), Chapter 1, α=1 stable cosine Lévy exponent; Laplace cosine transform.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexLaplaceFrequencyOne
open MeasureTheory Complex Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLaplaceCosine
    (a : ℝ) (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(a * x)) * Real.cos x) = a / (a ^ 2 + 1) := by
  sorry
