-- Prove2me | Theorems.Thm_GlobalTheory_submoduleOf_saturationIn
-- name    : GlobalTheory.submoduleOf_saturationIn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:39.904898+00:00
-- url     : https://prove2.me/theorems/52e059a6-1947-4cb1-bfc4-786f96e40737
-- title:
--   Global Theory: submodule Of saturation In
-- statement:
--   The Global Theory construction uses the submodule Of saturation In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L476-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L476-L479

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

theorem GlobalTheory.submoduleOf_saturationIn (M N : Submodule R V) :
    (saturationIn M N).submoduleOf M = saturation (N.submoduleOf M) := by sorry
