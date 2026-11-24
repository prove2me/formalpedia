-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_Lcomp_rankOne
-- name    : GlobalTheory.BK.mem_Lcomp_rankOne
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:12.477795+00:00
-- url     : https://prove2.me/theorems/1df61eeb-f00e-4af6-b406-f0f9e7051eea
-- title:
--   BK: mem Lcomp rank One
-- statement:
--   The BK construction uses the mem Lcomp rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L599-L608
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L599-L608

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

theorem GlobalTheory.BK.mem_Lcomp_rankOne {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n)
    {v : Unit → K⟦X⟧} :
    v ∈ (rankOne O K l e j).Lcomp τ ↔ ∃ m ∈ A O K, v () = E K l e ^ n * m := by sorry
