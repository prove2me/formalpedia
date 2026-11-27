-- Prove2me | Theorems.Thm_GlobalTheory_saturation_smul
-- name    : GlobalTheory.saturation_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:09.031074+00:00
-- url     : https://prove2.me/theorems/cf2d2fcf-12b6-555d-993e-88c7c439ffbe
-- title:
--   Global Theory: saturation smul
-- statement:
--   The Global Theory construction uses the saturation smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L315-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L315-L323

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

theorem GlobalTheory.saturation_smul [IsDomain R] (N : Submodule R M) {a : R} (ha : a ≠ 0) :
    saturation (a • N) = saturation N := by sorry
