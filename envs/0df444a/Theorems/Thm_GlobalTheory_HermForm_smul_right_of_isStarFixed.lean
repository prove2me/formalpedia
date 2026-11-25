-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_smul_right_of_isStarFixed
-- name    : GlobalTheory.HermForm.smul_right_of_isStarFixed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:08.441738+00:00
-- url     : https://prove2.me/theorems/5efaad2c-f38d-4aaf-892e-f5b976aa8768
-- title:
--   Herm Form: smul right of is Star Fixed
-- statement:
--   The Herm Form construction uses the smul right of is Star Fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L510-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L510-L513

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

theorem GlobalTheory.HermForm.smul_right_of_isStarFixed {F R M : Type*} [CommRing F] [CommRing R] [StarRing R]
    [Algebra F R] [IsStarFixed F R] [AddCommGroup M] [Module R M] [Module F M]
    [IsScalarTower F R M] (h : HermForm R M) (a : F) (x y : M) : h x (a • y) = a • h x y := by sorry
