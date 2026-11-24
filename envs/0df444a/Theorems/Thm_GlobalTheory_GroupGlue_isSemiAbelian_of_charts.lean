-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_isSemiAbelian_of_charts
-- name    : GlobalTheory.GroupGlue.isSemiAbelian_of_charts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:40.67707+00:00
-- url     : https://prove2.me/theorems/9d9755db-a558-42fe-b710-13ed888f0379
-- title:
--   Group Glue: is Semi Abelian of charts
-- statement:
--   The Group Glue construction uses the is Semi Abelian of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L330-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L330-L367

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
variable [∀ i, GrpObj (H i)]
variable [GrpObj G]

theorem GlobalTheory.GroupGlue.isSemiAbelian_of_charts (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) (hs : ∀ i, IsSemiAbelian (H i)) :
    IsSemiAbelian G := by sorry
