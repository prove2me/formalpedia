-- Prove2me | Theorems.Thm_GlobalTheory_saturationIn_smul_left
-- name    : GlobalTheory.saturationIn_smul_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:21.064152+00:00
-- url     : https://prove2.me/theorems/d9004f48-8fa6-4c6d-9332-47963dce5ad8
-- title:
--   Global Theory: saturation In smul left
-- statement:
--   The Global Theory construction uses the saturation In smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L977-L979
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L977-L979

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

theorem GlobalTheory.saturationIn_smul_left (M N : Submodule R V) {c : K} (hc : c ≠ 0) :
    saturationIn (c • M) N = c • saturationIn M N := by sorry
