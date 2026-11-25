-- Prove2me | Theorems.Thm_GlobalTheory_map_saturatedOrderIsoSubspaceSpan_apply
-- name    : GlobalTheory.map_saturatedOrderIsoSubspaceSpan_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:23.307212+00:00
-- url     : https://prove2.me/theorems/a811be2e-e74f-4c62-83d8-adc8c3e766cd
-- title:
--   Global Theory: map saturated Order Iso Subspace Span apply
-- statement:
--   The Global Theory construction uses the map saturated Order Iso Subspace Span apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L905-L913
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L905-L913

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

theorem GlobalTheory.map_saturatedOrderIsoSubspaceSpan_apply (M : Submodule R V)
    (N : {N : Submodule R M // IsSaturatedSubmodule N}) :
    (saturatedOrderIsoSubspaceSpan K M N).map (Submodule.span K (M : Set V)).subtype =
      Submodule.span K (N.1.map M.subtype : Set V) := by sorry
