-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedSubmodule_comap_restrictScalars
-- name    : GlobalTheory.isSaturatedSubmodule_comap_restrictScalars
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:00.494061+00:00
-- url     : https://prove2.me/theorems/cd7372b5-c7c5-44f9-ae0f-9116a9ba5c6a
-- title:
--   Global Theory: is Saturated Submodule comap restrict Scalars
-- statement:
--   The Global Theory construction uses the is Saturated Submodule comap restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L865-L867
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L865-L867

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
variable {K}

theorem GlobalTheory.isSaturatedSubmodule_comap_restrictScalars {M : Type*} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] V) (W : Submodule K V) :
    IsSaturatedSubmodule ((W.restrictScalars R).comap f) := by sorry
