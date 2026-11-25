-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_Nondegenerate_ext_left
-- name    : GlobalTheory.HermForm.Nondegenerate.ext_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:20.676703+00:00
-- url     : https://prove2.me/theorems/0befe4bd-0160-432d-8bc1-a0abcc35f8c5
-- title:
--   Nondegenerate: ext left
-- statement:
--   The Nondegenerate construction uses the ext left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L135-L137

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

theorem GlobalTheory.HermForm.Nondegenerate.ext_left (H : h.Nondegenerate) {x x' : M} (hx : ∀ y, h x y = h x' y) :
    x = x' := by sorry
