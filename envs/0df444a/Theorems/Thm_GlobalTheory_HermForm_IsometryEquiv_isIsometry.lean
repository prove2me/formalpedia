-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_IsometryEquiv_isIsometry
-- name    : GlobalTheory.HermForm.IsometryEquiv.isIsometry
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:58.651727+00:00
-- url     : https://prove2.me/theorems/49407bdd-bf77-550f-bdb0-22818e29f5f1
-- title:
--   Isometry Equiv: is Isometry
-- statement:
--   The Isometry Equiv construction uses the is Isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L211-L212

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
open GlobalTheory.HermForm.IsometryEquiv
variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}

theorem GlobalTheory.HermForm.IsometryEquiv.isIsometry (f : h₁.IsometryEquiv h₂) : h₁.IsIsometry h₂ f.toLinearEquiv.toLinearMap := by sorry
