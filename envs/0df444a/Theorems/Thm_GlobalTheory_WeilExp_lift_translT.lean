-- Prove2me | Theorems.Thm_GlobalTheory_WeilExp_lift_translT
-- name    : GlobalTheory.WeilExp.lift_translT
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:20.475104+00:00
-- url     : https://prove2.me/theorems/74ac501b-efa4-4df6-a301-a0a2bbcaf458
-- title:
--   Weil Exp: lift transl T
-- statement:
--   The Weil Exp construction uses the lift transl T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L43-L45

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

theorem GlobalTheory.WeilExp.lift_translT {W : Over S} (p : W ⟶ T) (q : W ⟶ A) (x : T ⟶ A) :
    lift p q ≫ Out.translT A x = lift p ((p ≫ x) * q) := by sorry
