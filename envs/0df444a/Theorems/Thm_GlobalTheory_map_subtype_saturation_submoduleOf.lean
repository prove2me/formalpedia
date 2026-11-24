-- Prove2me | Theorems.Thm_GlobalTheory_map_subtype_saturation_submoduleOf
-- name    : GlobalTheory.map_subtype_saturation_submoduleOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:27.016831+00:00
-- url     : https://prove2.me/theorems/b925b304-e118-4f05-8930-b34aaf48fec9
-- title:
--   Global Theory: map subtype saturation submodule Of
-- statement:
--   The Global Theory construction uses the map subtype saturation submodule Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L481-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L481-L483

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

theorem GlobalTheory.map_subtype_saturation_submoduleOf (M N : Submodule R V) :
    (saturation (N.submoduleOf M)).map M.subtype = saturationIn M N := by sorry
