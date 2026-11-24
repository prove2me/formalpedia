-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_flat
-- name    : GlobalTheory.SmallExtLift.mem_of_flat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:14:49.378953+00:00
-- url     : https://prove2.me/theorems/dc90b0aa-54c8-45fd-89fd-6ab360b41274
-- title:
--   Small Ext Lift: mem of flat
-- statement:
--   The Small Ext Lift construction uses the mem of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L110-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L110-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]

theorem GlobalTheory.SmallExtLift.mem_of_flat [IsLocalRing R] {ε : R} (hε : ε ≠ 0) {B : Type} [CommRing B] (c : R →+* B)
    (hf : c.Flat) (a : B) (ha : c ε * a = 0) : a ∈ (IsLocalRing.maximalIdeal R).map c := by sorry
