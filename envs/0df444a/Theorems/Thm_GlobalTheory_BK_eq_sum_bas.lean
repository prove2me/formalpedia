-- Prove2me | Theorems.Thm_GlobalTheory_BK_eq_sum_bas
-- name    : GlobalTheory.BK.eq_sum_bas
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:00.384115+00:00
-- url     : https://prove2.me/theorems/9c2f9f47-1fa9-4298-9b19-e25658609ac8
-- title:
--   BK: eq sum bas
-- statement:
--   The BK construction uses the eq sum bas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L136-L140

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

theorem GlobalTheory.BK.eq_sum_bas [Fintype ι] [DecidableEq ι] (v : Vec K a ι) :
    v = ∑ i, (fun τ => v τ i) • (bas i : Vec K a ι) := by sorry
