-- Prove2me | Theorems.Thm_GlobalTheory_map_subtype_saturation
-- name    : GlobalTheory.map_subtype_saturation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:11.606258+00:00
-- url     : https://prove2.me/theorems/f9e4623d-dec2-47e5-a3c1-e9d07abba4a9
-- title:
--   Global Theory: map subtype saturation
-- statement:
--   The Global Theory construction uses the map subtype saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L471-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L471-L474

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

theorem GlobalTheory.map_subtype_saturation (M : Submodule R V) (N : Submodule R M) :
    (saturation N).map M.subtype = saturationIn M (N.map M.subtype) := by sorry
