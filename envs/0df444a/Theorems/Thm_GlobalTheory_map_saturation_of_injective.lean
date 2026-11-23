-- Prove2me | Theorems.Thm_GlobalTheory_map_saturation_of_injective
-- name    : GlobalTheory.map_saturation_of_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:04.335363+00:00
-- url     : https://prove2.me/theorems/49738509-12f5-48e3-a415-47f85cc85410
-- title:
--   Global Theory: map saturation of injective
-- statement:
--   The Global Theory construction uses the map saturation of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L238-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L238-L250

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

theorem GlobalTheory.map_saturation_of_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
    (N : Submodule R M) :
    (saturation N).map f = LinearMap.range f ⊓ saturation (N.map f) := by sorry
