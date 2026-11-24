-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_Nondegenerate_eq_zero_right
-- name    : GlobalTheory.HermForm.Nondegenerate.eq_zero_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:57.738053+00:00
-- url     : https://prove2.me/theorems/df87275b-e6c0-416a-bb6f-9099e197aef2
-- title:
--   Nondegenerate: eq zero right
-- statement:
--   The Nondegenerate construction uses the eq zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L132-L133

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

theorem GlobalTheory.HermForm.Nondegenerate.eq_zero_right (H : h.Nondegenerate) {y : M} (hy : ∀ x, h x y = 0) : y = 0 := by sorry
