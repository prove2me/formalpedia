-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedIn_iff_isTorsionFree
-- name    : GlobalTheory.isSaturatedIn_iff_isTorsionFree
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:38.583086+00:00
-- url     : https://prove2.me/theorems/8b35a731-d505-5441-9d91-49068bbe1ab1
-- title:
--   Global Theory: is Saturated In iff is Torsion Free
-- statement:
--   The Global Theory construction uses the is Saturated In iff is Torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L511-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L511-L513

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

theorem GlobalTheory.isSaturatedIn_iff_isTorsionFree [IsDomain R] {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ Module.IsTorsionFree R (M ⧸ N.submoduleOf M) := by sorry
