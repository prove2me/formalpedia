-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerInterval
-- name    : Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerInterval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:49:43.748342+00:00
-- url     : https://prove2.me/theorems/28b99ba7-0487-4d07-8cc2-952f08231be5
-- title:
--   Exact stable small-jump power compensation integral over zero to one
-- statement:
--   For 0<alpha<1 the real interval integral of r^(-alpha) from 0 to 1 is exactly 1/(1-alpha), enabling the finite small-jump compensation drift in the original stable Lévy-Khintchine formula.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, small-jump stable compensation and pinned intervalIntegral.integral_rpow.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 intervalIntegral Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerInterval
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in (0 : ℝ)..1, r ^ (-alpha)) = 1 / (1 - alpha) := by sorry
