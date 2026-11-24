-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_conj_mem_lieN
-- name    : GlobalTheory.Tw.PFlag.conj_mem_lieN
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:48.899473+00:00
-- url     : https://prove2.me/theorems/76034fbe-2d47-4942-9efb-99777854c4ba
-- title:
--   PFlag: conj mem lie N
-- statement:
--   The PFlag construction uses the conj mem lie N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L144-L145

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

theorem GlobalTheory.Tw.PFlag.conj_mem_lieN {g : GL (Fin n) k} (hg : g ∈ F.stab) {X : Matrix (Fin n) (Fin n) k} (hX : X ∈ F.lieN) :
    g.val * X * g⁻¹.val ∈ F.lieN := by sorry
