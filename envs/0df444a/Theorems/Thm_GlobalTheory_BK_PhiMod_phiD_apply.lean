-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_phiD_apply
-- name    : GlobalTheory.BK.PhiMod.phiD_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:30:50.482874+00:00
-- url     : https://prove2.me/theorems/7510c905-8279-46cd-863d-5c1b2b4c85d4
-- title:
--   Phi Mod: phi D apply
-- statement:
--   The Phi Mod construction uses the phi D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L253-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L253-L253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)

theorem GlobalTheory.BK.PhiMod.phiD_apply (d : P.D) (τ : ZMod a) : P.phiD d τ = P.mx0 τ *ᵥ d (τ - 1) := by sorry
