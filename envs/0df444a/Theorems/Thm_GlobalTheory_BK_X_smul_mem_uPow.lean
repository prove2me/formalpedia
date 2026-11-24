-- Prove2me | Theorems.Thm_GlobalTheory_BK_X_smul_mem_uPow
-- name    : GlobalTheory.BK.X_smul_mem_uPow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:24.855328+00:00
-- url     : https://prove2.me/theorems/4d6fcef1-ea20-437c-a3b9-8b4e4e459f29
-- title:
--   BK: X smul mem u Pow
-- statement:
--   The BK construction uses the X smul mem u Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L61-L62

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

theorem GlobalTheory.BK.X_smul_mem_uPow (w : Vec K a ι) : (X : K⟦X⟧) • w ∈ uPow K a ι 1 := by sorry
