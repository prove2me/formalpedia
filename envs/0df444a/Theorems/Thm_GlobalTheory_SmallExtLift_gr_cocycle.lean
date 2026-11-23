-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_gr_cocycle
-- name    : GlobalTheory.SmallExtLift.gr_cocycle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:52.724833+00:00
-- url     : https://prove2.me/theorems/2961cf4a-7733-40c5-ba21-f2eaaa9e0725
-- title:
--   Small Ext Lift: gr cocycle
-- statement:
--   The Small Ext Lift construction uses the gr cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L145-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L145-L153

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

theorem GlobalTheory.SmallExtLift.gr_cocycle {M : LB X} (hM : M.IsLB) (f : Z ⟶ X) (z : Z) {i j k : M.ι} (hi : f z ∈ M.U i)
    (hj : f z ∈ M.U j) (hk : f z ∈ M.U k) :
    gr f z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val * gr f z (M.U j ⊓ M.U k) ⟨hj, hk⟩ (M.g j k).val =
      gr f z (M.U i ⊓ M.U k) ⟨hi, hk⟩ (M.g i k).val := by sorry
