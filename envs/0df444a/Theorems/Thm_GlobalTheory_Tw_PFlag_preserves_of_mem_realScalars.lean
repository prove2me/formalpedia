-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_preserves_of_mem_realScalars
-- name    : GlobalTheory.Tw.PFlag.preserves_of_mem_realScalars
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:12.904797+00:00
-- url     : https://prove2.me/theorems/bb6e4a15-a623-483e-a6f1-c50ca4b3ddca
-- title:
--   PFlag: preserves of mem real Scalars
-- statement:
--   The PFlag construction uses the preserves of mem real Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L355-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L355-L358

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
variable {n : ℕ}
open GlobalTheory.Tw.PFlag
variable {F : PFlag n ℂ}

theorem GlobalTheory.Tw.PFlag.preserves_of_mem_realScalars {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ F.realScalars) :
    ∀ V ∈ F.carrier, ∀ v ∈ F.summand V, X *ᵥ v ∈ F.summand V := by sorry
