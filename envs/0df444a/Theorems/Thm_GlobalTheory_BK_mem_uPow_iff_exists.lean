-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_uPow_iff_exists
-- name    : GlobalTheory.BK.mem_uPow_iff_exists
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:38.810856+00:00
-- url     : https://prove2.me/theorems/f16cf79d-5a59-4544-9004-d0cc1a30a599
-- title:
--   BK: mem u Pow iff exists
-- statement:
--   The BK construction uses the mem u Pow iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L52-L59

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

theorem GlobalTheory.BK.mem_uPow_iff_exists {m : ℕ} {v : Vec K a ι} :
    v ∈ uPow K a ι m ↔ ∃ w : Vec K a ι, v = (X : K⟦X⟧) ^ m • w := by sorry
