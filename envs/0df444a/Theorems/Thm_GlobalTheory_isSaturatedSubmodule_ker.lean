-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_ker
-- name    : GlobalTheory.isSaturatedSubmodule_ker
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:12.986415+00:00
-- url     : https://prove2.me/theorems/c4df8168-4b66-4665-95e5-8392e3a812ef
-- title:
--   Global Theory: is Saturated Submodule ker
-- statement:
--   The Global Theory construction uses the is Saturated Submodule ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L222-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L222-L228

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

theorem GlobalTheory.isSaturatedSubmodule_ker [IsDomain R] [Module.IsTorsionFree R M'] (f : M →ₗ[R] M') :
    IsSaturatedSubmodule (LinearMap.ker f) := by sorry
