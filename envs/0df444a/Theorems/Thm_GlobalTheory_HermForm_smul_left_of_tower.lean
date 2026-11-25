-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_smul_left_of_tower
-- name    : GlobalTheory.HermForm.smul_left_of_tower
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:05.82825+00:00
-- url     : https://prove2.me/theorems/631a0337-45b7-4e2a-96c0-52be88c89121
-- title:
--   Herm Form: smul left of tower
-- statement:
--   The Herm Form construction uses the smul left of tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L515-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L515-L519

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

theorem GlobalTheory.HermForm.smul_left_of_tower {S R M : Type*} [CommRing S] [CommRing R] [StarRing R]
    [Algebra S R] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] (h : HermForm R M) (a : S) (x y : M) :
    h (a • x) y = algebraMap S R a * h x y := by sorry
