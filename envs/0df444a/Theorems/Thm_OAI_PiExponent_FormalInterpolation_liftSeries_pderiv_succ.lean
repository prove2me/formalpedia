-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_liftSeries_pderiv_succ
-- name    : OAI.PiExponent.FormalInterpolation.liftSeries_pderiv_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:15:45.735741+00:00
-- url     : https://prove2.me/theorems/96c370ec-5bab-44c7-b977-c35e2c165d4c
-- title:
--   Lifted univariate series have zero successor-coordinate derivative
-- statement:
--   A series lifted from one variable into the formal jet depends only on coordinate zero, so its partial derivative in any successor coordinate is zero.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Mathlib.RingTheory.MvPowerSeries.Derivative

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.liftSeries_pderiv_succ
    {m : Nat} (i : Fin m) (f : PowerSeries Complex) :
    MvPowerSeries.pderiv Complex i.succ (liftSeries m f) = 0 := by
  sorry
