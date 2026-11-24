-- Prove2me | Theorems.Thm_GlobalTheory_map_saturation_le
-- name    : GlobalTheory.map_saturation_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:09:40.135805+00:00
-- url     : https://prove2.me/theorems/eed6cd70-2edd-46e7-bd8f-79b4ec6ba6c5
-- title:
--   Global Theory: map saturation le
-- statement:
--   The Global Theory construction uses the map saturation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L230-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L230-L236

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

theorem GlobalTheory.map_saturation_le (f : M →ₗ[R] M') (N : Submodule R M) :
    (saturation N).map f ≤ saturation (N.map f) := by sorry
