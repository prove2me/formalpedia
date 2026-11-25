-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieQ_single
-- name    : GlobalTheory.Tw.PFlag.mem_lieQ_single
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:33.036496+00:00
-- url     : https://prove2.me/theorems/e45aa7e5-07ec-4fb4-9f61-a10dffc307f6
-- title:
--   PFlag: mem lie Q single
-- statement:
--   The PFlag construction uses the mem lie Q single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L161-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L161-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)
variable {F}
variable (F)
variable {F}

theorem GlobalTheory.Tw.PFlag.mem_lieQ_single {V : Submodule k (Fin n → k)} {X : Matrix (Fin n) (Fin n) k} :
    X ∈ (single V).lieQ ↔ ∀ v ∈ V, X *ᵥ v ∈ V := by sorry
