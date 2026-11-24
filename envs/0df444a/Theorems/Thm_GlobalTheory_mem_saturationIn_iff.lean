-- Prove2me | Theorems.Thm_GlobalTheory_mem_saturationIn_iff
-- name    : GlobalTheory.mem_saturationIn_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:10.611877+00:00
-- url     : https://prove2.me/theorems/c7213dd5-42e1-47fa-8764-de1a86c13e86
-- title:
--   Global Theory: mem saturation In iff
-- statement:
--   The Global Theory construction uses the mem saturation In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L431-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L431-L433

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

theorem GlobalTheory.mem_saturationIn_iff [IsDomain R] {M N : Submodule R V} {x : V} :
    x ∈ saturationIn M N ↔ x ∈ M ∧ ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by sorry
