-- Prove2me | Theorems.Thm_GlobalTheory_saturation_eq_of_le_of_le
-- name    : GlobalTheory.saturation_eq_of_le_of_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:01.264355+00:00
-- url     : https://prove2.me/theorems/f1cbf4e8-d3ef-502e-8398-438656fb89c8
-- title:
--   Global Theory: saturation eq of le of le
-- statement:
--   The Global Theory construction uses the saturation eq of le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L140-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L140-L141

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

theorem GlobalTheory.saturation_eq_of_le_of_le {N P : Submodule R M} (h₁ : N ≤ P) (h₂ : P ≤ saturation N) :
    saturation P = saturation N := by sorry
