-- Prove2me | Theorems.Thm_GlobalTheory_map_saturationIn_of_injective
-- name    : GlobalTheory.map_saturationIn_of_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:18.202648+00:00
-- url     : https://prove2.me/theorems/ef7ed99f-c629-4f2d-92a7-c47e31d1f142
-- title:
--   Global Theory: map saturation In of injective
-- statement:
--   The Global Theory construction uses the map saturation In of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L546-L550
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L546-L550

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

theorem GlobalTheory.map_saturationIn_of_injective {f : V →ₗ[R] V'} (hf : Function.Injective f)
    (M N : Submodule R V) :
    (saturationIn M N).map f = saturationIn (M.map f) (N.map f) := by sorry
