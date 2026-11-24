-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieN_iff_trace
-- name    : GlobalTheory.Tw.PFlag.mem_lieN_iff_trace
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:20.303876+00:00
-- url     : https://prove2.me/theorems/e20138c4-9991-4b3d-a87e-e2480fbe3193
-- title:
--   PFlag: mem lie N iff trace
-- statement:
--   The PFlag construction uses the mem lie N iff trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L208-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L208-L228

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

theorem GlobalTheory.Tw.PFlag.mem_lieN_iff_trace {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieN ↔ ∀ Y ∈ F.lieQ, (X * Y).trace = 0 := by sorry
