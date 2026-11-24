-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_stab_iff_map
-- name    : GlobalTheory.Tw.PFlag.mem_stab_iff_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:09.861521+00:00
-- url     : https://prove2.me/theorems/ffb28da0-a12a-49ef-9e82-1f1a9b9315fa
-- title:
--   PFlag: mem stab iff map
-- statement:
--   The PFlag construction uses the mem stab iff map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L133-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L133-L142

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

theorem GlobalTheory.Tw.PFlag.mem_stab_iff_map {g : GL (Fin n) k} : g ∈ F.stab ↔ ∀ V ∈ F.carrier, V.map g.val.mulVecLin = V := by sorry
