-- Prove2me | Theorems.Thm_GlobalTheory_CMTensor_algebraMap_right_injective
-- name    : GlobalTheory.CMTensor.algebraMap_right_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:43.211781+00:00
-- url     : https://prove2.me/theorems/4a3df9ca-ac3f-42dc-ad0c-52455c31b410
-- title:
--   CMTensor: algebra Map right injective
-- statement:
--   The CMTensor construction uses the algebra Map right injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L897-L898
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L897-L898

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
universe u v
attribute [instance] HermModule.addCommGroup HermModule.module
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
attribute [simp] IsStarFixed.star_algebraMap
variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.CMTensor
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]

theorem GlobalTheory.CMTensor.algebraMap_right_injective : Function.Injective (algebraMap A (CMTensor E A)) := by sorry
