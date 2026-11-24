-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_Nondegenerate_ext_right
-- name    : GlobalTheory.HermForm.Nondegenerate.ext_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:50.047677+00:00
-- url     : https://prove2.me/theorems/42b4b926-96b4-4d03-b164-2104e6e5b9c5
-- title:
--   Nondegenerate: ext right
-- statement:
--   The Nondegenerate construction uses the ext right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L139-L141

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

theorem GlobalTheory.HermForm.Nondegenerate.ext_right (H : h.Nondegenerate) {y y' : M} (hy : ∀ x, h x y = h x y') :
    y = y' := by sorry
