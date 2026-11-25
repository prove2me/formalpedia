-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_isLocalizedModule_redQ
-- name    : GlobalTheory.BK.PhiMod.isLocalizedModule_redQ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:01.971104+00:00
-- url     : https://prove2.me/theorems/b249c864-b1c1-4cf4-8d42-2ace8fc972d4
-- title:
--   Phi Mod: is Localized Module red Q
-- statement:
--   The Phi Mod construction uses the is Localized Module red Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L329-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L329-L363

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
variable [NormedAlgebra ℚ_[l] K]

theorem GlobalTheory.BK.PhiMod.isLocalizedModule_redQ (τ : ZMod a) :
    IsLocalizedModule (Submonoid.powers (l : O)) (P.redQ τ) := by sorry
