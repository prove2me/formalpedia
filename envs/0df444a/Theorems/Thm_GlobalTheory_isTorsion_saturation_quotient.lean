-- Prove2me | Theorems.Thm_GlobalTheory_isTorsion_saturation_quotient
-- name    : GlobalTheory.isTorsion_saturation_quotient
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:25.424849+00:00
-- url     : https://prove2.me/theorems/19f692b3-0e53-484c-8253-d8bb537c0ddf
-- title:
--   Global Theory: is Torsion saturation quotient
-- statement:
--   The Global Theory construction uses the is Torsion saturation quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L325-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L325-L333

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

theorem GlobalTheory.isTorsion_saturation_quotient (N : Submodule R M) :
    Module.IsTorsion R (saturation N ⧸ N.submoduleOf (saturation N)) := by sorry
