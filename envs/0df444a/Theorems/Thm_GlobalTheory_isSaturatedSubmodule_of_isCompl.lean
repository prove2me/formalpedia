-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_of_isCompl
-- name    : GlobalTheory.isSaturatedSubmodule_of_isCompl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:29.524559+00:00
-- url     : https://prove2.me/theorems/f18563f8-3b9e-467c-b7c7-ae565331a911
-- title:
--   Global Theory: is Saturated Submodule of is Compl
-- statement:
--   The Global Theory construction uses the is Saturated Submodule of is Compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L286-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L286-L301

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

theorem GlobalTheory.isSaturatedSubmodule_of_isCompl [IsDomain R] [Module.IsTorsionFree R M]
    {N P : Submodule R M} (h : IsCompl N P) : IsSaturatedSubmodule N := by sorry
