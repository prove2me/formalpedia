-- Prove2me | Theorems.Thm_GlobalTheory_BK_geom_sub_mem
-- name    : GlobalTheory.BK.geom_sub_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:43:32.542206+00:00
-- url     : https://prove2.me/theorems/0f7c0907-4a07-42c1-b62b-d56104186d1d
-- title:
--   BK: geom sub mem
-- statement:
--   The BK construction uses the geom sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L88-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L88-L97

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
variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}

theorem GlobalTheory.BK.geom_sub_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) :
    geom T w - (∑ j ∈ Finset.range n, T ^ j) w ∈ uPow K a ι (n + 1) := by sorry
