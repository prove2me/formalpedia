-- Prove2me | Theorems.Thm_GlobalTheory_WeilExp_translT_translPt_comm
-- name    : GlobalTheory.WeilExp.translT_translPt_comm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:34.542455+00:00
-- url     : https://prove2.me/theorems/30cc2f20-0e2c-4738-94c4-32476888b35e
-- title:
--   Weil Exp: transl T transl Pt comm
-- statement:
--   The Weil Exp construction uses the transl T transl Pt comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L29-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_WeilIsExpRiemannForm
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
noncomputable section
open GlobalTheory GlobalTheory.WeilExp
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

theorem GlobalTheory.WeilExp.translT_translPt_comm [IsCommMonObj A] (x y : T ⟶ A) :
    (Out.translT A x).left ≫ (Out.translPt A y).left = (Out.translT A y).left ≫ (Out.translPt A x).left := by sorry
