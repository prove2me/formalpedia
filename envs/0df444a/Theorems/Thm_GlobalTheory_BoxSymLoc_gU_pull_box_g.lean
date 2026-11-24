-- Prove2me | Theorems.Thm_GlobalTheory_BoxSymLoc_gU_pull_box_g
-- name    : GlobalTheory.BoxSymLoc.gU_pull_box_g
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:09.956167+00:00
-- url     : https://prove2.me/theorems/5077ccc6-4489-40e7-8fd4-7ed3b7b09a75
-- title:
--   Box Sym Loc: g U pull box g
-- statement:
--   The Box Sym Loc construction uses the g U pull box g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedSymBoxLB.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedSymBoxLB.lean#L23-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedSymBoxLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxSymLoc
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res)
open ReciprocityTheory.ChartRestriction.G.Out.LBxP
variable {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

theorem GlobalTheory.BoxSymLoc.gU_pull_box_g (F : J → (X' ⟶ X)) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F (fun _ => 1)).U i ⊓ (LB.LinComb L F (fun _ => 1)).U j))
    (hy' : ∀ m, y ∈ (a ≫ F m) ⁻¹ᵁ (L.U (i m) ⊓ L.U (j m))) :
    gU y hy (pullU a _ ((LB.LinComb L F (fun _ => 1)).g i j)) =
      ∏ m, gU y (hy' m) (pullU (a ≫ F m) _ (L.g (i m) (j m))) := by sorry
