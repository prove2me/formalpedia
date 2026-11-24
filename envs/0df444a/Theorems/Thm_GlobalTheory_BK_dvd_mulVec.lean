-- Prove2me | Theorems.Thm_GlobalTheory_BK_dvd_mulVec
-- name    : GlobalTheory.BK.dvd_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:27.405577+00:00
-- url     : https://prove2.me/theorems/a5987072-97c2-4e0b-9cfc-f00cab88db85
-- title:
--   BK: dvd mul Vec
-- statement:
--   The BK construction uses the dvd mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L64-L65

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

theorem GlobalTheory.BK.dvd_mulVec [Fintype ι] {c : K⟦X⟧} (Y : Matrix κ ι K⟦X⟧) {v : ι → K⟦X⟧} (hv : ∀ i, c ∣ v i)
    (j : κ) : c ∣ (Y *ᵥ v) j := by sorry
