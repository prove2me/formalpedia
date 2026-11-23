-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_mul_eq_zero_of_mem
-- name    : GlobalTheory.SmallExtLift.mul_eq_zero_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:47.837591+00:00
-- url     : https://prove2.me/theorems/8523d0e8-1830-4fd6-b027-e68e79352aca
-- title:
--   Small Ext Lift: mul eq zero of mem
-- statement:
--   The Small Ext Lift construction uses the mul eq zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L134-L143

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

theorem GlobalTheory.SmallExtLift.mul_eq_zero_of_mem {B : Type*} [CommRing B] (c : R →+* B) {I : Ideal R} {ε : R}
    (h : ∀ a ∈ I, a * ε = 0) {b : B} (hb : b ∈ I.map c) : c ε * b = 0 := by sorry
