-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieN
-- name    : GlobalTheory.Tw.PFlag.mem_lieN
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:21.301271+00:00
-- url     : https://prove2.me/theorems/10e18100-e49a-5e3c-a95f-1385d6a52994
-- title:
--   PFlag: mem lie N
-- statement:
--   The PFlag construction uses the mem lie N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L90-L90

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

theorem GlobalTheory.Tw.PFlag.mem_lieN {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieN ↔ ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V := by sorry
