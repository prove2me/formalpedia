-- Prove2me | Theorems.Thm_GlobalTheory_BK_Hom_app_xi
-- name    : GlobalTheory.BK.Hom.app_xi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:55.426891+00:00
-- url     : https://prove2.me/theorems/4f116643-6ad7-4851-9bab-38e2afbaa49a
-- title:
--   Hom: app xi
-- statement:
--   The Hom construction uses the app xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L474-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L474-L475

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
open GlobalTheory.BK.Hom
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)

theorem GlobalTheory.BK.Hom.app_xi (d : P.D) : F.app (P.xi d) = Q.xi (F.onD d) := by sorry
