-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SectionsGroupRank_neg_f
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank.neg_f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:37.837265+00:00
-- url     : https://prove2.me/theorems/a861b769-8f1d-47f1-865c-96e0a3920c4f
-- title:
--   Sections Group Rank: neg f
-- statement:
--   The Sections Group Rank construction uses the neg f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SectionsGroupRank.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SectionsGroupRank.lean#L89-L89

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank.neg_f (s : Secs A L a T) (j) : LB.Sec.f (-s) j = - LB.Sec.f s j := by sorry
