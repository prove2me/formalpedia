-- Prove2me | Theorems.Thm_GlobalTheory_ThetaModelGroup_hom_ext_points
-- name    : GlobalTheory.ThetaModelGroup.hom_ext_points
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:12.927625+00:00
-- url     : https://prove2.me/theorems/bacf1954-86dc-4fa0-9269-f576c489d9a5
-- title:
--   Theta Model Group: hom ext points
-- statement:
--   The Theta Model Group construction uses the hom ext points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L160-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L160-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}

theorem GlobalTheory.ThetaModelGroup.hom_ext_points (H : PointCriterion) (h1 : IsReduced Y.left) (h2 : LocallyOfFiniteType Y.hom)
    {κ : Type} {D : κ → X.left.Opens} (hD : ⨆ c, D c = ⊤) (ha : ∀ c, IsAffineOpen (D c)) (f g : Y ⟶ X)
    (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y ≫ f = y ≫ g) : f = g := by sorry
