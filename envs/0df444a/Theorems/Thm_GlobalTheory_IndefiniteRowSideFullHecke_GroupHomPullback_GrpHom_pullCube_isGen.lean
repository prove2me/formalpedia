-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GroupHomPullback_GrpHom_pullCube_isGen
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.GrpHom.pullCube_isGen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:51.446749+00:00
-- url     : https://prove2.me/theorems/2db31bc5-759c-4989-be7b-9ce1b93d3443
-- title:
--   Grp Hom: pull Cube is Gen
-- statement:
--   The Grp Hom construction uses the pull Cube is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L355-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L355-L357

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{u}}
open GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.GrpHom
variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {G : Over S} [GrpObj G] [IsCommMonObj G]
  (f : GrpHom G' G)

theorem GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.GrpHom.pullCube_isGen (L : LB G.left) {t : LB.Gen (Theta G L)} (ht : t.IsGen) :
    (f.pullCube L t).IsGen := by sorry
