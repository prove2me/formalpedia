-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_unitaryGroup_smul_app_left
-- name    : GlobalTheory.HermForm.unitaryGroup.smul_app_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:51.605425+00:00
-- url     : https://prove2.me/theorems/ecff6eda-436f-4c13-8d2d-509b7d8a9039
-- title:
--   unitary Group: smul app left
-- statement:
--   The unitary Group construction uses the smul app left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L300-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L300-L301

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
open GlobalTheory.HermForm.unitaryGroup

theorem GlobalTheory.HermForm.unitaryGroup.smul_app_left (g : h.unitaryGroup) (x y : M) : h (g • x) y = h x (g⁻¹ • y) := by sorry
