-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_stab_iff
-- name    : GlobalTheory.Tw.PFlag.mem_stab_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:38.523304+00:00
-- url     : https://prove2.me/theorems/741bfd0c-98f3-4801-bab5-4fbcddec1601
-- title:
--   PFlag: mem stab iff
-- statement:
--   The PFlag construction uses the mem stab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L174-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L174-L179

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
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}

theorem GlobalTheory.Tw.PFlag.mem_stab_iff {g : GL (Fin n) k} : g ∈ F.stab ↔ g.val ∈ F.lieQ := by sorry
