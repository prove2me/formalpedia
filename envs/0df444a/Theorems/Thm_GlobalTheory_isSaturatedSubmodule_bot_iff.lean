-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_bot_iff
-- name    : GlobalTheory.isSaturatedSubmodule_bot_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:31.822189+00:00
-- url     : https://prove2.me/theorems/05984576-7697-492d-9414-585c5a81d13a
-- title:
--   Global Theory: is Saturated Submodule bot iff
-- statement:
--   The Global Theory construction uses the is Saturated Submodule bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L157-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

theorem GlobalTheory.isSaturatedSubmodule_bot_iff [IsDomain R] :
    IsSaturatedSubmodule (⊥ : Submodule R M) ↔ Module.IsTorsionFree R M := by sorry
