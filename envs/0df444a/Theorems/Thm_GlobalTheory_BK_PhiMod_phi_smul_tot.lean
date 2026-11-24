-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_phi_smul_tot
-- name    : GlobalTheory.BK.PhiMod.phi_smul_tot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:34.436008+00:00
-- url     : https://prove2.me/theorems/997a2182-75a9-4396-80e5-aba9d4459baf
-- title:
--   Phi Mod: phi smul tot
-- statement:
--   The Phi Mod construction uses the phi smul tot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L265-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L265-L271

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
variable [Fact l.Prime]

theorem GlobalTheory.BK.PhiMod.phi_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.phi (f • v) = frobTot K a l f • P.phi v := by sorry
