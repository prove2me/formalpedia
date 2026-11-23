-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
-- name    : GlobalTheory.SmallExtLift.gr_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:39.09238+00:00
-- url     : https://prove2.me/theorems/7c9ced9f-f211-4c12-8233-2b6a271597c3
-- title:
--   Small Ext Lift: gr ext
-- statement:
--   The Small Ext Lift construction uses the gr ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L39-L41

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

theorem GlobalTheory.SmallExtLift.gr_ext {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ x (hx : (𝟙 X : X ⟶ X) x ∈ V), gr (𝟙 X) x V hx a = gr (𝟙 X) x V hx b) : a = b := by sorry
