-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_isIsometry_iff_comap
-- name    : GlobalTheory.HermForm.isIsometry_iff_comap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:10.54443+00:00
-- url     : https://prove2.me/theorems/7a306e54-cd98-5256-8019-c61d3182d469
-- title:
--   Herm Form: is Isometry iff comap
-- statement:
--   The Herm Form construction uses the is Isometry iff comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L163-L165

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

theorem GlobalTheory.HermForm.isIsometry_iff_comap {h₁ : HermForm R M} {h₂ : HermForm R N} {f : M →ₗ[R] N} :
    h₁.IsIsometry h₂ f ↔ h₂.comap f = h₁ := by sorry
