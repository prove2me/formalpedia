-- Prove2me | Theorems.Thm_GlobalTheory_finrank_saturationIn
-- name    : GlobalTheory.finrank_saturationIn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:09.869982+00:00
-- url     : https://prove2.me/theorems/517b46dc-1360-57e8-83fa-b8b566054d11
-- title:
--   Global Theory: finrank saturation In
-- statement:
--   The Global Theory construction uses the finrank saturation In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L559-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L559-L560

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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']

theorem GlobalTheory.finrank_saturationIn [IsDomain R] {M N : Submodule R V} [Module.Finite R M] (h : N ≤ M) :
    Module.finrank R (saturationIn M N) = Module.finrank R N := by sorry
