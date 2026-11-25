-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_zero_right
-- name    : GlobalTheory.HermForm.zero_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:14.748455+00:00
-- url     : https://prove2.me/theorems/a5704d8b-8ec8-4019-867a-18561f45261c
-- title:
--   Herm Form: zero right
-- statement:
--   The Herm Form construction uses the zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L57-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (h : HermForm R M)

theorem GlobalTheory.HermForm.zero_right (x : M) : h x 0 = 0 := by sorry
