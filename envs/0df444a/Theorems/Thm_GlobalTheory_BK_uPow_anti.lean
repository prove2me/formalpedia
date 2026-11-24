-- Prove2me | Theorems.Thm_GlobalTheory_BK_uPow_anti
-- name    : GlobalTheory.BK.uPow_anti
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:41.116174+00:00
-- url     : https://prove2.me/theorems/5f2c35c7-09b2-45db-9683-e46aee3fa4c6
-- title:
--   BK: u Pow anti
-- statement:
--   The BK construction uses the u Pow anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L42-L43

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

theorem GlobalTheory.BK.uPow_anti {m n : ℕ} (h : m ≤ n) : uPow K a ι n ≤ uPow K a ι m := by sorry
