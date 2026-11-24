-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeGen_one_left_fst
-- name    : GlobalTheory.AbLaw.CubeGen.one_left_fst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:51:02.346739+00:00
-- url     : https://prove2.me/theorems/4bbac109-fbbc-4bb1-b26c-9afce5246d37
-- title:
--   Cube Gen: one left fst
-- statement:
--   The Cube Gen construction uses the one left fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L330-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L330-L332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
variable {A}

theorem GlobalTheory.AbLaw.CubeGen.one_left_fst {S' : Scheme.{0}} (f : S' ⟶ S) (T : Over S') :
    (1 : T ⟶ (Over.pullback f).obj A).left ≫ pullback.fst A.hom f = (T.hom ≫ f) ≫ η[A].left := by sorry
