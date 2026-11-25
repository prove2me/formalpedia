-- Prove2me | Theorems.Thm_GlobalTheory_mem_saturation_iff_mem_span
-- name    : GlobalTheory.mem_saturation_iff_mem_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:02.7315+00:00
-- url     : https://prove2.me/theorems/88279de6-275e-4466-a474-60fead51ea77
-- title:
--   Global Theory: mem saturation iff mem span
-- statement:
--   The Global Theory construction uses the mem saturation iff mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L834-L849
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L834-L849

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

theorem GlobalTheory.mem_saturation_iff_mem_span {M : Submodule R V} {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ (x : V) ∈ Submodule.span K (N.map M.subtype : Set V) := by sorry
