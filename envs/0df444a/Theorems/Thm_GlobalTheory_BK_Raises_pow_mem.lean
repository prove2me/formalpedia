-- Prove2me | Theorems.Thm_GlobalTheory_BK_Raises_pow_mem
-- name    : GlobalTheory.BK.Raises.pow_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:46.618091+00:00
-- url     : https://prove2.me/theorems/06465d62-d0e0-4cb6-b5ce-66def2801134
-- title:
--   Raises: pow mem
-- statement:
--   The Raises construction uses the pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L82-L86

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

theorem GlobalTheory.BK.Raises.pow_mem {T : Module.End K (Vec K a ι)} (hT : Raises T) {w : Vec K a ι}
    (hw : w ∈ uPow K a ι 1) (n : ℕ) : (T ^ n) w ∈ uPow K a ι (n + 1) := by sorry
