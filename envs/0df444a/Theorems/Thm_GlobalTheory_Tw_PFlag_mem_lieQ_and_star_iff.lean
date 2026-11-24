-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieQ_and_star_iff
-- name    : GlobalTheory.Tw.PFlag.mem_lieQ_and_star_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:31.687021+00:00
-- url     : https://prove2.me/theorems/0fb769ca-8cde-4488-8adf-5ec5237d2235
-- title:
--   PFlag: mem lie Q and star iff
-- statement:
--   The PFlag construction uses the mem lie Q and star iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L323-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L323-L342

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

theorem GlobalTheory.Tw.PFlag.mem_lieQ_and_star_iff {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ F.lieQ ∧ Xᴴ ∈ F.lieQ ↔ ∀ V ∈ F.carrier, ∀ v ∈ F.summand V, X *ᵥ v ∈ F.summand V := by sorry
