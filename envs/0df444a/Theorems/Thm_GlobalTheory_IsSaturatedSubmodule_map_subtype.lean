-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_map_subtype
-- name    : GlobalTheory.IsSaturatedSubmodule.map_subtype
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:39.206827+00:00
-- url     : https://prove2.me/theorems/4b8bc2f3-e06b-5c83-95d3-902b188b46ec
-- title:
--   Is Saturated Submodule: map subtype
-- statement:
--   The Is Saturated Submodule construction uses the map subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L269-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L269-L284

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

theorem GlobalTheory.IsSaturatedSubmodule.map_subtype {P : Submodule R M} {N : Submodule R P}
    (hN : IsSaturatedSubmodule N) (hP : IsSaturatedSubmodule P) :
    IsSaturatedSubmodule (N.map P.subtype) := by sorry
