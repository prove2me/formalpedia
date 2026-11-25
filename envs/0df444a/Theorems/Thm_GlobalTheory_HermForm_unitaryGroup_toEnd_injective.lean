-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_unitaryGroup_toEnd_injective
-- name    : GlobalTheory.HermForm.unitaryGroup.toEnd_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:21.584667+00:00
-- url     : https://prove2.me/theorems/08c406e7-6111-4943-87fe-780327e0fe49
-- title:
--   unitary Group: to End injective
-- statement:
--   The unitary Group construction uses the to End injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L325-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L325-L326

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
variable {h}
open GlobalTheory.HermForm.unitaryGroup

theorem GlobalTheory.HermForm.unitaryGroup.toEnd_injective : Function.Injective (toEnd h) := by sorry
