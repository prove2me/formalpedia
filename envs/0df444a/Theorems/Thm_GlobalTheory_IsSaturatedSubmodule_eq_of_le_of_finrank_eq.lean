-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_eq_of_le_of_finrank_eq
-- name    : GlobalTheory.IsSaturatedSubmodule.eq_of_le_of_finrank_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:01.467566+00:00
-- url     : https://prove2.me/theorems/bd01c0d1-8d34-40af-aeb0-63a3a1f26654
-- title:
--   Is Saturated Submodule: eq of le of finrank eq
-- statement:
--   The Is Saturated Submodule construction uses the eq of le of finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L412-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L412-L414

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

theorem GlobalTheory.IsSaturatedSubmodule.eq_of_le_of_finrank_eq [Module.Finite R M] {N P : Submodule R M}
    (hN : IsSaturatedSubmodule N) (h : N ≤ P) (hr : Module.finrank R N = Module.finrank R P) :
    N = P := by sorry
