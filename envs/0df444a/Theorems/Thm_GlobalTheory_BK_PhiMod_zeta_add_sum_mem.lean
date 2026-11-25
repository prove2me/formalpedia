-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_add_sum_mem
-- name    : GlobalTheory.BK.PhiMod.zeta_add_sum_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:24.893599+00:00
-- url     : https://prove2.me/theorems/29b57fda-5579-5dfd-95ce-7da06cbcb317
-- title:
--   Phi Mod: zeta add sum mem
-- statement:
--   The Phi Mod construction uses the zeta add sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L443-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L443-L447

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

theorem GlobalTheory.BK.PhiMod.zeta_add_sum_mem (y : Vec K a ι) (m : ℕ) :
    P.zeta y + ∑ n ∈ Finset.range m, (P.lphi ^ (n + 1)) (P.conn y) ∈ uPow K a ι (m + 1) := by sorry
