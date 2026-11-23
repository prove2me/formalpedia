-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_gr_gen
-- name    : GlobalTheory.SmallExtLift.gr_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:31.919811+00:00
-- url     : https://prove2.me/theorems/5ea05752-c502-4f0b-8a63-40d0388f328d
-- title:
--   Small Ext Lift: gr gen
-- statement:
--   The Small Ext Lift construction uses the gr gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L158-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L158-L170

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

theorem GlobalTheory.SmallExtLift.gr_gen {M : LB X} {F : Y ⟶ X} {t : LB.Gen (M.pull F)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {i j : M.ι} (hi : F (r z) ∈ M.U i) (hj : F (r z) ∈ M.U j) :
    gr r z _ (pull_le M F i le_rfl hi) (t.s fun _ => i).val =
      gr (r ≫ F) z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val *
        gr r z _ (pull_le M F j le_rfl hj) (t.s fun _ => j).val := by sorry
