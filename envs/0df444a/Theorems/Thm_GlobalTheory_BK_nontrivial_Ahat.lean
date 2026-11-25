-- Prove2me | Theorems.Thm_GlobalTheory_BK_nontrivial_Ahat
-- name    : GlobalTheory.BK.nontrivial_Ahat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:23.139348+00:00
-- url     : https://prove2.me/theorems/10b4c895-649f-402d-9998-4dabdac3c2d0
-- title:
--   BK: nontrivial Ahat
-- statement:
--   The BK construction uses the nontrivial Ahat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L642-L653
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L642-L653

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

theorem GlobalTheory.BK.nontrivial_Ahat [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] :
    Nontrivial (Ahat O K l e) := by sorry
