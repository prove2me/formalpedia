-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_smul_mem_iff
-- name    : GlobalTheory.IsSaturatedSubmodule.smul_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:08.584797+00:00
-- url     : https://prove2.me/theorems/2500cbb0-2a62-454d-a06d-c60732015106
-- title:
--   Is Saturated Submodule: smul mem iff
-- statement:
--   The Is Saturated Submodule construction uses the smul mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L106-L107

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

theorem GlobalTheory.IsSaturatedSubmodule.smul_mem_iff [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) {x : M} : a • x ∈ N ↔ x ∈ N := by sorry
