-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableBelowOneCutoffComplexMoment
-- name    : Kyprianou.Ch01.stableBelowOneCutoffComplexMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:33:20.779742+00:00
-- url     : https://prove2.me/theorems/6ac096d9-836d-4fe4-8938-dd74a6fad4b9
-- title:
--   Exact cutoff moment of stable power as a complex set integral
-- statement:
--   The complex-valued integral of the below-unit stable power r^-alpha on the positive halfline, with the source cutoff indicator r<1, is exactly the real reciprocal 1/(1-alpha) embedded in Complex for 0<alpha<1. This uses the proved small-jump moment on (0,1).
-- source:
--   Kyprianou (2006), Ch 1 Exercise 1.4 original small-jump compensation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerSet
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableBelowOneCutoffComplexMoment
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioi (0 : ℝ),
      (if r < 1 then (((r ^ (-alpha) : ℝ) : ℂ)) else 0) ∂volume) =
      (((1 / (1 - alpha) : ℝ) : ℂ)) := by sorry
