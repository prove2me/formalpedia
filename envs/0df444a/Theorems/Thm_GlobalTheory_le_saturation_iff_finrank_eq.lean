-- Prove2me | Theorems.Thm_GlobalTheory_le_saturation_iff_finrank_eq
-- name    : GlobalTheory.le_saturation_iff_finrank_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:11.70585+00:00
-- url     : https://prove2.me/theorems/8a5a9503-58bf-4442-b1e2-aa043c2aaa0c
-- title:
--   Global Theory: le saturation iff finrank eq
-- statement:
--   The Global Theory construction uses the le saturation iff finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L397-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L397-L410

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

theorem GlobalTheory.le_saturation_iff_finrank_eq [Module.Finite R M] {N P : Submodule R M} (h : N ≤ P) :
    P ≤ saturation N ↔ Module.finrank R N = Module.finrank R P := by sorry
