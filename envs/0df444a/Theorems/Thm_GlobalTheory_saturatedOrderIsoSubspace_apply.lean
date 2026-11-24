-- Prove2me | Theorems.Thm_GlobalTheory_saturatedOrderIsoSubspace_apply
-- name    : GlobalTheory.saturatedOrderIsoSubspace_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:20:32.098376+00:00
-- url     : https://prove2.me/theorems/0abc7d22-4653-47a2-9853-a697a65c1655
-- title:
--   Global Theory: saturated Order Iso Subspace apply
-- statement:
--   The Global Theory construction uses the saturated Order Iso Subspace apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L800-L803
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L800-L803

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
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f]

theorem GlobalTheory.saturatedOrderIsoSubspace_apply (N : {N : Submodule R M // IsSaturatedSubmodule N}) :
    saturatedOrderIsoSubspace K f N = Submodule.span K (f '' N.1) := by sorry
