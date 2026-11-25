-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PullbackGroupAction_pullGrp_comm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction.pullGrp_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:26.912312+00:00
-- url     : https://prove2.me/theorems/f7381cdc-c803-5861-bb44-de1c6883d1c0
-- title:
--   Pullback Group Action: pull Grp comm
-- statement:
--   The Pullback Group Action construction uses the pull Grp comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PullbackGroupAction.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PullbackGroupAction.lean#L18-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PullbackGroupAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}}

theorem GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction.pullGrp_comm (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] : IsCommMonObj (pullGrp f G) := by sorry
