-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedIn_iff_exists_subspace
-- name    : GlobalTheory.isSaturatedIn_iff_exists_subspace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:26.760289+00:00
-- url     : https://prove2.me/theorems/8bfc6c96-b741-481a-9f6d-07c3b8a2024a
-- title:
--   Global Theory: is Saturated In iff exists subspace
-- statement:
--   The Global Theory construction uses the is Saturated In iff exists subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L874-L880
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L874-L880

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

theorem GlobalTheory.isSaturatedIn_iff_exists_subspace {M N : Submodule R V} :
    IsSaturatedIn M N ↔ ∃ W : Submodule K V, M ⊓ W.restrictScalars R = N := by sorry
