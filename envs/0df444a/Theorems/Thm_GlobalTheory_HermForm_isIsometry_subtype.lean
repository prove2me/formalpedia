-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_isIsometry_subtype
-- name    : GlobalTheory.HermForm.isIsometry_subtype
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:58.852113+00:00
-- url     : https://prove2.me/theorems/070465fd-c3de-4c70-b713-966ec2420d6b
-- title:
--   Herm Form: is Isometry subtype
-- statement:
--   The Herm Form construction uses the is Isometry subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L178-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L178-L179

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

theorem GlobalTheory.HermForm.isIsometry_subtype (h : HermForm R M) (W : Submodule R M) :
    (h.restrict W).IsIsometry h W.subtype := by sorry
