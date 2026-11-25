-- Prove2me | Theorems.Thm_GlobalTheory_BK_one_notMem_Lcomp_rankOne
-- name    : GlobalTheory.BK.one_notMem_Lcomp_rankOne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:34.730181+00:00
-- url     : https://prove2.me/theorems/590d5af7-ad7a-416d-9ff6-d88826da720e
-- title:
--   BK: one not Mem Lcomp rank One
-- statement:
--   The BK construction uses the one not Mem Lcomp rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L614-L623
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L614-L623

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

theorem GlobalTheory.BK.one_notMem_Lcomp_rankOne (τ : ZMod a) :
    (fun _ => 1) ∉ (rankOne O K l e fun _ : ZMod a => 1).Lcomp τ := by sorry
