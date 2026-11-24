-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_uPow
-- name    : GlobalTheory.BK.mem_uPow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:23.4578+00:00
-- url     : https://prove2.me/theorems/414ae08c-6dc6-4db7-bd68-86a99ecd23b2
-- title:
--   BK: mem u Pow
-- statement:
--   The BK construction uses the mem u Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L39-L40

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

theorem GlobalTheory.BK.mem_uPow {m : ℕ} {v : Vec K a ι} : v ∈ uPow K a ι m ↔ ∀ τ i, (X : K⟦X⟧) ^ m ∣ v τ i := by sorry
