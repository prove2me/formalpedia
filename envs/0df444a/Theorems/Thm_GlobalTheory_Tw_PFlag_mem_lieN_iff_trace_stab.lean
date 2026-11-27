-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieN_iff_trace_stab
-- name    : GlobalTheory.Tw.PFlag.mem_lieN_iff_trace_stab
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:31.043241+00:00
-- url     : https://prove2.me/theorems/e7d9de80-8328-529f-ad9b-36f0c7359ae7
-- title:
--   PFlag: mem lie N iff trace stab
-- statement:
--   The PFlag construction uses the mem lie N iff trace stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L230-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L230-L241

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

theorem GlobalTheory.Tw.PFlag.mem_lieN_iff_trace_stab [Infinite k] {X : Matrix (Fin n) (Fin n) k} :
    X ∈ F.lieN ↔ ∀ g ∈ F.stab, (X * g.val).trace = 0 := by sorry
