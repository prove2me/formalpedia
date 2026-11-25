-- Prove2me | Theorems.Thm_GlobalTheory_BK_invE_invL_S_le_RpiE
-- name    : GlobalTheory.BK.invE_invL_S_le_RpiE
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:26.102823+00:00
-- url     : https://prove2.me/theorems/fcb5d8cd-3a25-4dfb-81f7-f84b2aae89a6
-- title:
--   BK: inv E inv L S le Rpi E
-- statement:
--   The BK construction uses the inv E inv L S le Rpi E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L500-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L500-L501

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
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable {O K}

theorem GlobalTheory.BK.invE_invL_S_le_RpiE : invE l e (invL l (S O K e)) ≤ RpiE O K l e := by sorry
