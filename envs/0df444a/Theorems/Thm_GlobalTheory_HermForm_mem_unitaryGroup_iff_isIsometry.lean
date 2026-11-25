-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_mem_unitaryGroup_iff_isIsometry
-- name    : GlobalTheory.HermForm.mem_unitaryGroup_iff_isIsometry
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:58.881719+00:00
-- url     : https://prove2.me/theorems/b5d51164-bd28-4805-9d35-c849058a0eae
-- title:
--   Herm Form: mem unitary Group iff is Isometry
-- statement:
--   The Herm Form construction uses the mem unitary Group iff is Isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L288-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L288-L289

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

theorem GlobalTheory.HermForm.mem_unitaryGroup_iff_isIsometry {g : M ≃ₗ[R] M} :
    g ∈ h.unitaryGroup ↔ h.IsIsometry h g.toLinearMap := by sorry
