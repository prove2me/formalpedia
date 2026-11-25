-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedIn_map_subtype_iff
-- name    : GlobalTheory.isSaturatedIn_map_subtype_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:39.370192+00:00
-- url     : https://prove2.me/theorems/0982c560-734b-597a-8759-2b9efcf94b9a
-- title:
--   Global Theory: is Saturated In map subtype iff
-- statement:
--   The Global Theory construction uses the is Saturated In map subtype iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L505-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L505-L509

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

theorem GlobalTheory.isSaturatedIn_map_subtype_iff {M : Submodule R V} {N : Submodule R M} :
    IsSaturatedIn M (N.map M.subtype) ↔ IsSaturatedSubmodule N := by sorry
