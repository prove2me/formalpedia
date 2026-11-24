-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul_tot
-- name    : GlobalTheory.BK.PhiMod.conn_smul_tot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:00.692041+00:00
-- url     : https://prove2.me/theorems/c24086ee-c543-4570-ae77-54f9ee57b483
-- title:
--   Phi Mod: conn smul tot
-- statement:
--   The Phi Mod construction uses the conn smul tot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L334-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L334-L339

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
variable (P : PhiMod O K l e a ι)

theorem GlobalTheory.BK.PhiMod.conn_smul_tot (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.conn (f • v) = NTot f • v + f • P.conn v := by sorry
