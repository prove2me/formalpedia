-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_plusProj_app
-- name    : GlobalTheory.BK.PhiMod.plusProj_app
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:43:49.739326+00:00
-- url     : https://prove2.me/theorems/ebdf18d2-c215-402a-8d36-0d55d753f602
-- title:
--   Phi Mod: plus Proj app
-- statement:
--   The Phi Mod construction uses the plus Proj app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L572-L577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L572-L577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
variable [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem GlobalTheory.BK.PhiMod.plusProj_app (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (P.plusProj hy).app (join v f) = fun τ _ => f τ := by sorry
