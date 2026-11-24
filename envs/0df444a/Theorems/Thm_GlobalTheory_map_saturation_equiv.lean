-- Prove2me | Theorems.Thm_GlobalTheory_map_saturation_equiv
-- name    : GlobalTheory.map_saturation_equiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:09:24.61339+00:00
-- url     : https://prove2.me/theorems/4cb044a7-471f-4769-bb3e-9042572aeff5
-- title:
--   Global Theory: map saturation equiv
-- statement:
--   The Global Theory construction uses the map saturation equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L252-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L252-L254

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

theorem GlobalTheory.map_saturation_equiv (e : M ≃ₗ[R] M') (N : Submodule R M) :
    (saturation N).map (e : M →ₗ[R] M') = saturation (N.map (e : M →ₗ[R] M')) := by sorry
