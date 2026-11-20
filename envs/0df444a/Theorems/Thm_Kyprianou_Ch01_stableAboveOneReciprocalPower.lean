-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneReciprocalPower
-- name    : Kyprianou.Ch01.stableAboveOneReciprocalPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:58:13.112172+00:00
-- url     : https://prove2.me/theorems/d1fbfdeb-948a-48b4-bd11-26e3bf67c0d4
-- title:
--   Positive-radius reciprocal stable power identity
-- statement:
--   At every strictly positive radius, the stable negative power density is equal to the inverse of the positive power denominator in Complex.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneReciprocalPower (alpha r : ℝ) (hr : 0 < r) :
    (((r ^ (-alpha - 1) : ℝ) : ℂ)) =
      (((r ^ (alpha + 1) : ℝ) : ℂ))⁻¹ := by sorry
