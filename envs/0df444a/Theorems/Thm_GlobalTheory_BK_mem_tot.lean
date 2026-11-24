-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_tot
-- name    : GlobalTheory.BK.mem_tot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:30:38.266642+00:00
-- url     : https://prove2.me/theorems/7490686a-7487-470c-a189-d67095822a05
-- title:
--   BK: mem tot
-- statement:
--   The BK construction uses the mem tot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesVecReduceModUMulVec.lean#L29-L30

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

theorem GlobalTheory.BK.mem_tot {B : Subalgebra O K⟦X⟧} {P : ZMod a → Submodule B (ι → K⟦X⟧)} {v : Vec K a ι} :
    v ∈ tot P ↔ ∀ τ, v τ ∈ P τ := by sorry
