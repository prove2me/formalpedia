-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_unip_iff
-- name    : GlobalTheory.Tw.PFlag.mem_unip_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:37.343638+00:00
-- url     : https://prove2.me/theorems/bce8f0ba-a675-5be8-a2bd-1ab027a1d989
-- title:
--   PFlag: mem unip iff
-- statement:
--   The PFlag construction uses the mem unip iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L181-L183

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

theorem GlobalTheory.Tw.PFlag.mem_unip_iff {g : GL (Fin n) k} : g ∈ F.unip ↔ g.val - 1 ∈ F.lieN := by sorry
