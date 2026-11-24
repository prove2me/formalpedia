-- Prove2me | Theorems.Thm_GlobalTheory_rank_inf_restrictScalars
-- name    : GlobalTheory.rank_inf_restrictScalars
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:15:08.825337+00:00
-- url     : https://prove2.me/theorems/ba33bb18-fd37-46ef-b6a7-58ef9e031226
-- title:
--   Global Theory: rank inf restrict Scalars
-- statement:
--   The Global Theory construction uses the rank inf restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L948-L951
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L948-L951

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

theorem GlobalTheory.rank_inf_restrictScalars {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Module.rank R (M ⊓ W.restrictScalars R : Submodule R V) = Module.rank K W := by sorry
