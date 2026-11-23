-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_gr_cst
-- name    : GlobalTheory.SmallExtLift.gr_cst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:11.417797+00:00
-- url     : https://prove2.me/theorems/07a99449-e1d1-42d3-8a6e-4eba93137cab
-- title:
--   Small Ext Lift: gr cst
-- statement:
--   The Small Ext Lift construction uses the gr cst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L55-L57

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

theorem GlobalTheory.SmallExtLift.gr_cst (f : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of R)) (z : Z) (V : X.Opens) (h : f z ∈ V)
    (r : R) : gr f z V h (cst p V r) = cstS (f ≫ p) z r := by sorry
