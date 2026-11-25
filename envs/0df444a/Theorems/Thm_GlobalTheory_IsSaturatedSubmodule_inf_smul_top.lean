-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_inf_smul_top
-- name    : GlobalTheory.IsSaturatedSubmodule.inf_smul_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:32.175807+00:00
-- url     : https://prove2.me/theorems/27beecca-6efb-548c-8595-b7cb197e2503
-- title:
--   Is Saturated Submodule: inf smul top
-- statement:
--   The Is Saturated Submodule construction uses the inf smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L303-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L303-L313

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

theorem GlobalTheory.IsSaturatedSubmodule.inf_smul_top [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) :
    N ⊓ a • (⊤ : Submodule R M) = a • N := by sorry
