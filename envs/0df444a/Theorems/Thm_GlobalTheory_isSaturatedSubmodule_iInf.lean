-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_iInf
-- name    : GlobalTheory.isSaturatedSubmodule_iInf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:59.818952+00:00
-- url     : https://prove2.me/theorems/656e0b51-8675-4542-9263-2cc93c75d40d
-- title:
--   Global Theory: is Saturated Submodule i Inf
-- statement:
--   The Global Theory construction uses the is Saturated Submodule i Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L204-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L204-L210

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

theorem GlobalTheory.isSaturatedSubmodule_iInf {ι : Sort*} {N : ι → Submodule R M}
    (h : ∀ i, IsSaturatedSubmodule (N i)) : IsSaturatedSubmodule (⨅ i, N i) := by sorry
