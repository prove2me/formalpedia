-- Prove2me | Theorems.Thm_GlobalTheory_BK_phiD_rankOne
-- name    : GlobalTheory.BK.phiD_rankOne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:53.006364+00:00
-- url     : https://prove2.me/theorems/5ebf37bc-b190-4470-b2e3-befea0512039
-- title:
--   BK: phi D rank One
-- statement:
--   The BK construction uses the phi D rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L610-L612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L610-L612

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
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {O K l e a}

theorem GlobalTheory.BK.phiD_rankOne {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n)
    (d : (rankOne O K l e j).D) : (rankOne O K l e j).phiD d τ () = (l : K) ^ n * d (τ - 1) () := by sorry
