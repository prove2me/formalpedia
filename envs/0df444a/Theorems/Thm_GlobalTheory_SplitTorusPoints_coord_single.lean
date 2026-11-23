-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorusPoints_coord_single
-- name    : GlobalTheory.SplitTorusPoints.coord_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:38.137957+00:00
-- url     : https://prove2.me/theorems/89aed51a-8d6d-4c69-af9b-56df015f5990
-- title:
--   Split Torus Points: coord single
-- statement:
--   The Split Torus Points construction uses the coord single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitTorusPointsMulEquiv.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitTorusPointsMulEquiv.lean#L84-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SplitTorusPoints
open Rosenlicht
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}

theorem GlobalTheory.SplitTorusPoints.coord_single (t : Z ⟶ splitTorus S X) (x : X) :
    (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (charUnit S X x).val := by sorry
