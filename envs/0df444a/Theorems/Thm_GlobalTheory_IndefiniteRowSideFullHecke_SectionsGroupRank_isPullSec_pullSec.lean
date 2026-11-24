-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SectionsGroupRank_isPullSec_pullSec
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank.isPullSec_pullSec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:31.205937+00:00
-- url     : https://prove2.me/theorems/f40447aa-5e06-4eb9-99ea-1000ff625b3a
-- title:
--   Sections Group Rank: is Pull Sec pull Sec
-- statement:
--   The Sections Group Rank construction uses the is Pull Sec pull Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SectionsGroupRank.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SectionsGroupRank.lean#L138-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SectionsGroupRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
variable {A} {L : LB A.left} {a : ℤ} {T : Over S}

theorem GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank.isPullSec_pullSec {T' : Over S} (u : T' ⟶ T) (s : Secs A L a T) :
    IsPullSec A L a (u ▷ A) (whiskerRight_snd _ _) s (pullSec u s) := by sorry
