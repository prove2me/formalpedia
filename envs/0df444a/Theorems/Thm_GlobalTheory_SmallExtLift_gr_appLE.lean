-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_gr_appLE
-- name    : GlobalTheory.SmallExtLift.gr_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:03.3146+00:00
-- url     : https://prove2.me/theorems/da956d3f-0447-4f17-9391-cf3338c71731
-- title:
--   Small Ext Lift: gr app LE
-- statement:
--   The Small Ext Lift construction uses the gr app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L31-L34

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

theorem GlobalTheory.SmallExtLift.gr_appLE (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ g ⁻¹ᵁ U)
    (h : f z ∈ V) (a : Γ(X, U)) :
    gr f z V h ((g.appLE U V e).hom a) = gr (f ≫ g) z U (e h) a := by sorry
