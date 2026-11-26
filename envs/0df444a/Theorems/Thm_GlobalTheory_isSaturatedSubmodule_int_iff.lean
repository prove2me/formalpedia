-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_int_iff
-- name    : GlobalTheory.isSaturatedSubmodule_int_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:18.00188+00:00
-- url     : https://prove2.me/theorems/c91e7671-6199-4eb9-9ae5-550dd7e4fb9f
-- title:
--   Global Theory: is Saturated Submodule int iff
-- statement:
--   The Global Theory construction uses the is Saturated Submodule int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L335-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L335-L344

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

theorem GlobalTheory.isSaturatedSubmodule_int_iff {A : Type*} [AddCommGroup A] (N : Submodule ℤ A) :
    IsSaturatedSubmodule N ↔ N.toAddSubgroup.NSMulSaturated := by sorry
