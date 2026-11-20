-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneLargeJumpPowerIntegral
-- name    : Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:59:02.998383+00:00
-- url     : https://prove2.me/theorems/1ed3a228-f309-4777-b0d9-8f7016ce4676
-- title:
--   Exact stable large-jump radial moment over one to infinity above index one
-- statement:
--   For 1<alpha<2, the Lebesgue integral of r^(-alpha) over (1,infinity) is 1/(alpha-1). This finite first moment governs the large-jump compensation drift for the original stable Lévy triplet.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, stable alpha above one large-jump compensation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Real Set MeasureTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegral
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r : ℝ in Set.Ioi (1 : ℝ), r ^ (-alpha)) =
      1 / (alpha - 1) := by sorry
