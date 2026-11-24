-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_vecs
-- name    : GlobalTheory.BK.mem_vecs
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:36:10.915594+00:00
-- url     : https://prove2.me/theorems/e9910b0f-9857-463b-bb08-9506c8a5fe48
-- title:
--   BK: mem vecs
-- statement:
--   The BK construction uses the mem vecs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L24-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
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
variable {O K : Type} [CommRing O] [NormedField K] [Algebra O K] {a : ℕ} {ι : Type}

theorem GlobalTheory.BK.mem_vecs {B : Subalgebra O K⟦X⟧} {v : ι → K⟦X⟧} : v ∈ vecs ι B ↔ ∀ i, v i ∈ B := by sorry
