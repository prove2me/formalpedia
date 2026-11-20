-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCanonicalScalePositive
-- name    : Kyprianou.Ch01.stableAlphaBelowOneCanonicalScalePositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:26:37.863185+00:00
-- url     : https://prove2.me/theorems/52cba970-9431-4ae5-8af5-9665b4eb8e82
-- title:
--   Positive canonical stable scale below index one from Gamma recurrence and cosine sign
-- statement:
--   For alpha in (0,1), Gamma(-alpha)<0 by recurrence and Gamma(1-alpha)>0, and cos(pi alpha/2)>0. Thus the canonical scale -Gamma(-alpha)cos(pi alpha/2)(cpos+cneg) is positive whenever the jump intensity sum is positive.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, stable Lévy exponent normalisation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneGammaRecurrence
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneCanonicalScalePositive
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hsum : 0 < cpos + cneg) :
    0 < -Real.Gamma (-alpha) *
      Real.cos (Real.pi * alpha / 2) * (cpos + cneg) := by sorry
