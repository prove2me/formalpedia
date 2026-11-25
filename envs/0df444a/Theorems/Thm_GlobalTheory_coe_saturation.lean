-- Prove2me | Theorems.Thm_GlobalTheory_coe_saturation
-- name    : GlobalTheory.coe_saturation
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:02.199911+00:00
-- url     : https://prove2.me/theorems/b74a2956-7536-46e3-915e-9e316471da49
-- title:
--   Global Theory: coe saturation
-- statement:
--   The Global Theory construction uses the coe saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L40-L43

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

theorem GlobalTheory.coe_saturation [IsDomain R] (N : Submodule R M) :
    (saturation N : Set M) = {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ N} := by sorry
