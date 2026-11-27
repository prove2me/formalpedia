-- Prove2me | Theorems.Thm_GlobalTheory_finrank_inf_restrictScalars
-- name    : GlobalTheory.finrank_inf_restrictScalars
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:09.848949+00:00
-- url     : https://prove2.me/theorems/c9ce6f9e-d710-5fff-ac60-ef3aadc9d664
-- title:
--   Global Theory: finrank inf restrict Scalars
-- statement:
--   The Global Theory construction uses the finrank inf restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L955-L957
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L955-L957

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

theorem GlobalTheory.finrank_inf_restrictScalars {M : Submodule R V} {W : Submodule K V}
    [FiniteDimensional K W] (h : W ≤ Submodule.span K (M : Set V)) :
    Module.finrank R (M ⊓ W.restrictScalars R : Submodule R V) = Module.finrank K W := by sorry
