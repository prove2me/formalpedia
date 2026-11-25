-- Prove2me | Theorems.Thm_GlobalTheory_saturation_eq_comap_torsion
-- name    : GlobalTheory.saturation_eq_comap_torsion
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:06.581944+00:00
-- url     : https://prove2.me/theorems/d91189ae-c252-5a05-b02b-e831cb557ceb
-- title:
--   Global Theory: saturation eq comap torsion
-- statement:
--   The Global Theory construction uses the saturation eq comap torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L18-L19

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
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

theorem GlobalTheory.saturation_eq_comap_torsion (N : Submodule R M) :
    saturation N = (Submodule.torsion R (M ⧸ N)).comap N.mkQ := by sorry
