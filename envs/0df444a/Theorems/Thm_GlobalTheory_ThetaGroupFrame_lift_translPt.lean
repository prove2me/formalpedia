-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGroupFrame_lift_translPt
-- name    : GlobalTheory.ThetaGroupFrame.lift_translPt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:47.866392+00:00
-- url     : https://prove2.me/theorems/20787922-c527-425d-8856-05e3d47fe81f
-- title:
--   Theta Group Frame: lift transl Pt
-- statement:
--   The Theta Group Frame construction uses the lift transl Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L114-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame

theorem GlobalTheory.ThetaGroupFrame.lift_translPt {S : Scheme.{0}} (A : Over S) [GrpObj A] {T B : Over S} (p : B ⟶ T)
    (x : T ⟶ A) (y : B ⟶ A) : lift p y ≫ Out.translPt A x = (p ≫ x) * y := by sorry
