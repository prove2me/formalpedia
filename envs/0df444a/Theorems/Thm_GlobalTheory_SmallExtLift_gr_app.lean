-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_gr_app
-- name    : GlobalTheory.SmallExtLift.gr_app
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:47.122173+00:00
-- url     : https://prove2.me/theorems/034f6d92-e15d-454b-8bf6-e1ea53b95677
-- title:
--   Small Ext Lift: gr app
-- statement:
--   The Small Ext Lift construction uses the gr app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L28-L29

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

theorem GlobalTheory.SmallExtLift.gr_app (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    gr f z (g ⁻¹ᵁ U) h ((g.app U).hom a) = gr (f ≫ g) z U h a := by sorry
