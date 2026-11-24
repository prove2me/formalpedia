-- Prove2me | Theorems.Thm_GlobalTheory_BK_eq_zero_of_mem_uPow
-- name    : GlobalTheory.BK.eq_zero_of_mem_uPow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:42.611245+00:00
-- url     : https://prove2.me/theorems/9926914a-f4bc-49eb-bb78-99d81e2eea1f
-- title:
--   BK: eq zero of mem u Pow
-- statement:
--   The BK construction uses the eq zero of mem u Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L45-L47

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

theorem GlobalTheory.BK.eq_zero_of_mem_uPow {v : Vec K a ι} (h : ∀ m, v ∈ uPow K a ι (m + 1)) : v = 0 := by sorry
