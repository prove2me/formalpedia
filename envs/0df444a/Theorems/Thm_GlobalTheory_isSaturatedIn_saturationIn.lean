-- Prove2me | Theorems.Thm_GlobalTheory_isSaturatedIn_saturationIn
-- name    : GlobalTheory.isSaturatedIn_saturationIn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:46.625826+00:00
-- url     : https://prove2.me/theorems/738072c2-7be1-5d7a-b436-e1cd977c2d00
-- title:
--   Global Theory: is Saturated In saturation In
-- statement:
--   The Global Theory construction uses the is Saturated In saturation In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L463-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L463-L465

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

theorem GlobalTheory.isSaturatedIn_saturationIn (M N : Submodule R V) : IsSaturatedIn M (saturationIn M N) := by sorry
