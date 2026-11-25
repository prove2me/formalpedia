-- Prove2me | Theorems.Thm_GlobalTheory_rank_saturationIn
-- name    : GlobalTheory.rank_saturationIn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:15:29.336147+00:00
-- url     : https://prove2.me/theorems/09003e3d-851a-42e4-95f9-5827fa9db52e
-- title:
--   Global Theory: rank saturation In
-- statement:
--   The Global Theory construction uses the rank saturation In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L552-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L552-L557

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

theorem GlobalTheory.rank_saturationIn [IsDomain R] {M N : Submodule R V} (h : N ≤ M) :
    Module.rank R (saturationIn M N) = Module.rank R N := by sorry
