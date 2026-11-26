-- Prove2me | Theorems.Thm_GlobalTheory_mem_saturatedOrderIsoSubspaceSpan_symm_apply
-- name    : GlobalTheory.mem_saturatedOrderIsoSubspaceSpan_symm_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:50.997584+00:00
-- url     : https://prove2.me/theorems/eb020ff2-23b3-56e8-a730-ed27b453718c
-- title:
--   Global Theory: mem saturated Order Iso Subspace Span symm apply
-- statement:
--   The Global Theory construction uses the mem saturated Order Iso Subspace Span symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L915-L917
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L915-L917

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
variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem GlobalTheory.mem_saturatedOrderIsoSubspaceSpan_symm_apply (M : Submodule R V)
    (W : Submodule K (Submodule.span K (M : Set V))) (x : M) :
    x ∈ ((saturatedOrderIsoSubspaceSpan K M).symm W).1 ↔ M.inclusionSpan K x ∈ W := by sorry
