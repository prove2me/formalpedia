-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_inf
-- name    : GlobalTheory.IsSaturatedSubmodule.inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:52.441941+00:00
-- url     : https://prove2.me/theorems/1027cb67-9756-474f-9289-687f02769739
-- title:
--   Is Saturated Submodule: inf
-- statement:
--   The Is Saturated Submodule construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L199-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L199-L202

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

theorem GlobalTheory.IsSaturatedSubmodule.inf {N P : Submodule R M} (hN : IsSaturatedSubmodule N)
    (hP : IsSaturatedSubmodule P) : IsSaturatedSubmodule (N ⊓ P) := by sorry
