-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_map_equiv_iff
-- name    : GlobalTheory.isSaturatedSubmodule_map_equiv_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:01.855378+00:00
-- url     : https://prove2.me/theorems/b6858372-b683-55f3-9848-5cce11e11300
-- title:
--   Global Theory: is Saturated Submodule map equiv iff
-- statement:
--   The Global Theory construction uses the is Saturated Submodule map equiv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L256-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L256-L260

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

theorem GlobalTheory.isSaturatedSubmodule_map_equiv_iff (e : M ≃ₗ[R] M') {N : Submodule R M} :
    IsSaturatedSubmodule (N.map (e : M →ₗ[R] M')) ↔ IsSaturatedSubmodule N := by sorry
