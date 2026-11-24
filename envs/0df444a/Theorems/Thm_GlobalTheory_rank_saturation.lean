-- Prove2me | Theorems.Thm_GlobalTheory_rank_saturation
-- name    : GlobalTheory.rank_saturation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:40.771932+00:00
-- url     : https://prove2.me/theorems/fca15852-b831-4438-9af2-1723b51dee42
-- title:
--   Global Theory: rank saturation
-- statement:
--   The Global Theory construction uses the rank saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L359-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L359-L369

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

theorem GlobalTheory.rank_saturation (N : Submodule R M) :
    Module.rank R (saturation N) = Module.rank R N := by sorry
