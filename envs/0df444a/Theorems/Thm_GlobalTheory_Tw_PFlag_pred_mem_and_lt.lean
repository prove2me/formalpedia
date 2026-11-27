-- Prove2me | Theorems.Thm_GlobalTheory_Tw_PFlag_pred_mem_and_lt
-- name    : GlobalTheory.Tw.PFlag.pred_mem_and_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:07.81574+00:00
-- url     : https://prove2.me/theorems/520ce49c-9d33-4dc7-9eeb-7210a12819b3
-- title:
--   PFlag: pred mem and lt
-- statement:
--   The PFlag construction uses the pred mem and lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L199-L206

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

theorem GlobalTheory.Tw.PFlag.pred_mem_and_lt {V : Submodule k (Fin n → k)} (hV : V ≠ ⊥) : F.pred V ∈ F.carrier ∧ F.pred V < V := by sorry
