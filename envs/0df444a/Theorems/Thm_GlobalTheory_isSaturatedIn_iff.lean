-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedIn_iff
-- name    : GlobalTheory.isSaturatedIn_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:18.585895+00:00
-- url     : https://prove2.me/theorems/6e43397d-306f-4206-8601-ea1bbc1c648d
-- title:
--   Global Theory: is Saturated In iff
-- statement:
--   The Global Theory construction uses the is Saturated In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L493-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L493-L503

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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']

theorem GlobalTheory.isSaturatedIn_iff {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ IsSaturatedSubmodule (N.submoduleOf M) := by sorry
