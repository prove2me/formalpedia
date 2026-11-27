-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_bot
-- name    : GlobalTheory.isSaturatedSubmodule_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:41.809045+00:00
-- url     : https://prove2.me/theorems/1f4e2858-c2d7-4dc6-9d2e-1340ec1824a3
-- title:
--   Global Theory: is Saturated Submodule bot
-- statement:
--   The Global Theory construction uses the is Saturated Submodule bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L162-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L162-L163

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

theorem GlobalTheory.isSaturatedSubmodule_bot [IsDomain R] [Module.IsTorsionFree R M] :
    IsSaturatedSubmodule (⊥ : Submodule R M) := by sorry
