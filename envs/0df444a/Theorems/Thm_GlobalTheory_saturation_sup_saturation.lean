-- Prove2me | Theorems.Thm_GlobalTheory_saturation_sup_saturation
-- name    : GlobalTheory.saturation_sup_saturation
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:02.223706+00:00
-- url     : https://prove2.me/theorems/7705ee32-26c2-532c-8121-e7ed040f06f0
-- title:
--   Global Theory: saturation sup saturation
-- statement:
--   The Global Theory construction uses the saturation sup saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L192-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L192-L197

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

theorem GlobalTheory.saturation_sup_saturation (N P : Submodule R M) :
    saturation (saturation N ⊔ saturation P) = saturation (N ⊔ P) := by sorry
