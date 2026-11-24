-- Prove2me | Theorems.Thm_GlobalTheory_TorusTrivial_app_comp_topIso_inv
-- name    : GlobalTheory.TorusTrivial.app_comp_topIso_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:24.002721+00:00
-- url     : https://prove2.me/theorems/54944213-abe8-4086-8e01-ebcd7f04a973
-- title:
--   Torus Trivial: app comp top Iso inv
-- statement:
--   The Torus Trivial construction uses the app comp top Iso inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenAndBijectiveOfWeightUnits.lean#L136-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusTrivial

theorem GlobalTheory.TorusTrivial.app_comp_topIso_inv {Y Z : Scheme.{0}} (f : Y ⟶ Z) (V : Z.Opens) :
    f.app V ≫ (f ⁻¹ᵁ V).topIso.inv = V.topIso.inv ≫ (f ∣_ V).appTop := by sorry
