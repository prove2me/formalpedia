-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_Mhatc
-- name    : GlobalTheory.BK.mem_Mhatc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:14.376699+00:00
-- url     : https://prove2.me/theorems/66ca2670-25fe-4ecb-a0af-dddde98347e3
-- title:
--   BK: mem Mhatc
-- statement:
--   The BK construction uses the mem Mhatc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L518-L535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L518-L535

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
variable {ι}

theorem GlobalTheory.BK.mem_Mhatc {w : ι → AhatE O K l e} :
    w ∈ Mhatc O K l e ι ↔ ∀ i, ∃ x : Ahat O K l e, algebraMap _ _ x = w i := by sorry
