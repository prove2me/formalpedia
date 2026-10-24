-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_generator_pderiv
-- name    : OAI.PiExponent.FormalInterpolation.formalJet_generator_pderiv
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:09:50.970283+00:00
-- url     : https://prove2.me/theorems/22befe86-125b-4bd7-b8c1-738426779026
-- title:
--   Formal jet generators have the expected successor derivative
-- statement:
--   Differentiating the formal jet's generator images in coordinate `i.succ` gives one for that coordinate's image and zero for every other image.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Mathlib.RingTheory.MvPowerSeries.Derivative

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.formalJet_generator_pderiv {m : Nat} (c : Fin m → Complex) (i : Fin m) : ∀ j : Fin (m + 1), MvPowerSeries.pderiv Complex i.succ (Fin.cases (1 + MvPowerSeries.X 0) (fun k => MvPowerSeries.C (c k) + MvPowerSeries.X k.succ + liftSeries m (PowerSeries.log Complex)) j) = if j = i.succ then 1 else 0 := by sorry
