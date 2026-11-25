-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_comap_comp
-- name    : GlobalTheory.HermForm.comap_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:43.379835+00:00
-- url     : https://prove2.me/theorems/abfdeb34-8ed5-5d96-a4e7-8ea577392b64
-- title:
--   Herm Form: comap comp
-- statement:
--   The Herm Form construction uses the comap comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L95-L96

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

theorem GlobalTheory.HermForm.comap_comp (f : N →ₗ[R] M) (g : P →ₗ[R] N) :
    h.comap (f ∘ₗ g) = (h.comap f).comap g := by sorry
