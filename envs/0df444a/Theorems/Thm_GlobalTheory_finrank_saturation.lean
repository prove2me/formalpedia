-- Prove2me | Theorems.Thm_GlobalTheory_finrank_saturation
-- name    : GlobalTheory.finrank_saturation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:08.464314+00:00
-- url     : https://prove2.me/theorems/48a57025-70b8-5ca5-a4e5-6e205d6b3d23
-- title:
--   Global Theory: finrank saturation
-- statement:
--   The Global Theory construction uses the finrank saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L371-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L371-L372

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
variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]

theorem GlobalTheory.finrank_saturation [Module.Finite R M] (N : Submodule R M) :
    Module.finrank R (saturation N) = Module.finrank R N := by sorry
