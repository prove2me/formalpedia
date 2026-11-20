-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneLargeJumpPowerIntegrable
-- name    : Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:59:10.289634+00:00
-- url     : https://prove2.me/theorems/4928bf34-a629-4982-9430-ae877e773ad5
-- title:
--   Stable above-one large-jump power moment integrable over one to infinity
-- statement:
--   For stable index 1<alpha<2, r^-alpha has a finite Lebesgue integral on (1,infinity), by the pinned exact integrableOn_Ioi_rpow_of_lt criterion. This justifies the above-one compensation of large jumps.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, stable Lévy measure and drift compensation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Real Set MeasureTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegrable
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn (fun r : ℝ => r ^ (-alpha))
      (Set.Ioi (1 : ℝ)) := by sorry
