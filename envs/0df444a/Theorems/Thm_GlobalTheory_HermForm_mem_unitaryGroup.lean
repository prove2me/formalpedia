-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_mem_unitaryGroup
-- name    : GlobalTheory.HermForm.mem_unitaryGroup
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:23.484037+00:00
-- url     : https://prove2.me/theorems/0ca0f90c-06a7-4e82-83c1-7e4857c2dcbe
-- title:
--   Herm Form: mem unitary Group
-- statement:
--   The Herm Form construction uses the mem unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L285-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L285-L286

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

theorem GlobalTheory.HermForm.mem_unitaryGroup {g : M ≃ₗ[R] M} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h (g x) (g y) = h x y := by sorry
