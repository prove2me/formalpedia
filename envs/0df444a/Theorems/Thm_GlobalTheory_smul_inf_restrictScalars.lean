-- Prove2me | Theorems.Thm_GlobalTheory_smul_inf_restrictScalars
-- name    : GlobalTheory.smul_inf_restrictScalars
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:33.306691+00:00
-- url     : https://prove2.me/theorems/8dc53378-1ba1-4dc8-8f5f-69fb6e973dd0
-- title:
--   Global Theory: smul inf restrict Scalars
-- statement:
--   The Global Theory construction uses the smul inf restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L962-L973
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L962-L973

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
omit [IsFractionRing R K]

theorem GlobalTheory.smul_inf_restrictScalars (M : Submodule R V) (W : Submodule K V) {c : K} (hc : c ≠ 0) :
    c • M ⊓ W.restrictScalars R = c • (M ⊓ W.restrictScalars R) := by sorry
