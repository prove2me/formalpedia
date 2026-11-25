-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieQ
-- name    : GlobalTheory.Tw.PFlag.mem_lieQ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:03.820671+00:00
-- url     : https://prove2.me/theorems/4701cddb-169e-4d86-ba82-e0581f958190
-- title:
--   PFlag: mem lie Q
-- statement:
--   The PFlag construction uses the mem lie Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L88-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L88-L88

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

theorem GlobalTheory.Tw.PFlag.mem_lieQ {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieQ ↔ ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ V := by sorry
