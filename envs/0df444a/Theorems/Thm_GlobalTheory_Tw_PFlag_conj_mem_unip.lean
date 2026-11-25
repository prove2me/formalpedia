-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_conj_mem_unip
-- name    : GlobalTheory.Tw.PFlag.conj_mem_unip
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:12.126649+00:00
-- url     : https://prove2.me/theorems/86f9bf77-3f85-5f33-82a5-de484989a3a0
-- title:
--   PFlag: conj mem unip
-- statement:
--   The PFlag construction uses the conj mem unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L147-L151

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

theorem GlobalTheory.Tw.PFlag.conj_mem_unip {g u : GL (Fin n) k} (hg : g ∈ F.stab) (hu : u ∈ F.unip) : g * u * g⁻¹ ∈ F.unip := by sorry
