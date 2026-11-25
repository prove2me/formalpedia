-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_neg_left
-- name    : GlobalTheory.HermForm.neg_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:00.66089+00:00
-- url     : https://prove2.me/theorems/904dc5b3-f839-4b61-9777-d48a4fdb6cfd
-- title:
--   Herm Form: neg left
-- statement:
--   The Herm Form construction uses the neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L54-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L54-L54

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

theorem GlobalTheory.HermForm.neg_left (x y : M) : h (-x) y = -h x y := by sorry
