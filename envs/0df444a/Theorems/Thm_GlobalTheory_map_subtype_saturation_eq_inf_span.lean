-- Prove2me | Theorems.Thm_GlobalTheory_map_subtype_saturation_eq_inf_span
-- name    : GlobalTheory.map_subtype_saturation_eq_inf_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:09:35.620803+00:00
-- url     : https://prove2.me/theorems/3aa0040a-cdce-42c6-b11b-23a833072fe2
-- title:
--   Global Theory: map subtype saturation eq inf span
-- statement:
--   The Global Theory construction uses the map subtype saturation eq inf span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L829-L832
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L829-L832

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

theorem GlobalTheory.map_subtype_saturation_eq_inf_span (M : Submodule R V) (N : Submodule R M) :
    (saturation N).map M.subtype =
      M ⊓ (Submodule.span K (N.map M.subtype : Set V)).restrictScalars R := by sorry
