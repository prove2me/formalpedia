-- Prove2me | Theorems.Thm_GlobalTheory_le_saturation_of_rank_le
-- name    : GlobalTheory.le_saturation_of_rank_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:13.250207+00:00
-- url     : https://prove2.me/theorems/954a61ee-f3d9-486b-a005-45db89325ae9
-- title:
--   Global Theory: le saturation of rank le
-- statement:
--   The Global Theory construction uses the le saturation of rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L374-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L374-L395

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

theorem GlobalTheory.le_saturation_of_rank_le {N P : Submodule R M} (h : N ≤ P)
    (hN : Module.rank R N < Cardinal.aleph0) (hr : Module.rank R P ≤ Module.rank R N) :
    P ≤ saturation N := by sorry
