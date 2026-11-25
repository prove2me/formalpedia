-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_smul_right_of_tower
-- name    : GlobalTheory.HermForm.smul_right_of_tower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:54.800518+00:00
-- url     : https://prove2.me/theorems/00b087c6-dffe-4183-aa6c-979ada4f03e1
-- title:
--   Herm Form: smul right of tower
-- statement:
--   The Herm Form construction uses the smul right of tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L521-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L521-L525

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

theorem GlobalTheory.HermForm.smul_right_of_tower {S R M : Type*} [CommRing S] [CommRing R] [StarRing R]
    [Algebra S R] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] (h : HermForm R M) (a : S) (x y : M) :
    h x (a • y) = star (algebraMap S R a) * h x y := by sorry
