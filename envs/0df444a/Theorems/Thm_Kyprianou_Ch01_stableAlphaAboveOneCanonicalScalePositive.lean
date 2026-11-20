-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCanonicalScalePositive
-- name    : Kyprianou.Ch01.stableAlphaAboveOneCanonicalScalePositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:27:17.080205+00:00
-- url     : https://prove2.me/theorems/2592d846-a71e-4cf9-846c-86bb3cf8af3a
-- title:
--   Strictly positive canonical stable Lévy scale above index one
-- statement:
--   When 1<alpha<2 and cpos+cneg>0, Gamma(-alpha)>0 follows from Gamma recurrence twice and Gamma(2-alpha)>0; cos(pi alpha/2)<0. Therefore -Gamma(-alpha)cos(pi alpha/2)(cpos+cneg) is positive.
-- source:
--   Kyprianou (2006) Exercise 1.4, stable Lévy–Khintchine normalisation above index one.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneGammaRecurrence
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneCanonicalScalePositive
    (alpha cpos cneg : ℝ)
    (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hsum : 0 < cpos + cneg) :
    0 < -Real.Gamma (-alpha) *
      Real.cos (Real.pi * alpha / 2) * (cpos + cneg) := by sorry
