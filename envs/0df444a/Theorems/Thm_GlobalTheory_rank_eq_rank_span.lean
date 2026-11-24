-- Prove2me | Theorems.Thm_GlobalTheory_rank_eq_rank_span
-- name    : GlobalTheory.rank_eq_rank_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:15:00.933798+00:00
-- url     : https://prove2.me/theorems/7f70427c-f998-4766-87e0-a51467fcb5db
-- title:
--   Global Theory: rank eq rank span
-- statement:
--   The Global Theory construction uses the rank eq rank span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L941-L944
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L941-L944

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

theorem GlobalTheory.rank_eq_rank_span (N : Submodule R V) :
    Module.rank R N = Module.rank K (Submodule.span K (N : Set V)) := by sorry
