-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_toSesq_injective
-- name    : GlobalTheory.HermForm.toSesq_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:09.648337+00:00
-- url     : https://prove2.me/theorems/17b281cd-0084-4d41-8f85-a009561a8508
-- title:
--   Herm Form: to Sesq injective
-- statement:
--   The Herm Form construction uses the to Sesq injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L39-L40

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

theorem GlobalTheory.HermForm.toSesq_injective : Function.Injective (toSesq : HermForm R M → SesqForm R M) := by sorry
