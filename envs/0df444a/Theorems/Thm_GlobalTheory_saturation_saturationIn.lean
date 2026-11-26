-- Prove2me | Theorems.Thm_GlobalTheory_saturation_saturationIn
-- name    : GlobalTheory.saturation_saturationIn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:03.245642+00:00
-- url     : https://prove2.me/theorems/0859bff6-6040-5305-a4c0-d5b7a420fa8f
-- title:
--   Global Theory: saturation saturation In
-- statement:
--   The Global Theory construction uses the saturation saturation In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L467-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L467-L469

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

theorem GlobalTheory.saturation_saturationIn {M N : Submodule R V} (h : N ≤ M) :
    saturation (saturationIn M N) = saturation N := by sorry
