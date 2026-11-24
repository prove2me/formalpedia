-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeGen_exists_cube_chart
-- name    : GlobalTheory.AbLaw.CubeGen.exists_cube_chart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:50:57.29992+00:00
-- url     : https://prove2.me/theorems/44190393-ff64-4ee6-8afa-5e418004be1e
-- title:
--   Cube Gen: exists cube chart
-- statement:
--   The Cube Gen construction uses the exists cube chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L265-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L265-L292

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
omit [GrpObj A]

theorem GlobalTheory.AbLaw.CubeGen.exists_cube_chart {T : Scheme.{0}} (j : T ⟶ A.left) :
    ∃ q : ((Over.pullback (j ≫ A.hom)).obj A ⊗ (Over.pullback (j ≫ A.hom)).obj A).left ⟶ (G3 A).left,
      IsPullback q ((Over.pullback (j ≫ A.hom)).obj A ⊗ (Over.pullback (j ≫ A.hom)).obj A).hom (x3 A 2).left j ∧
      q ≫ (x3 A 0).left = (fst _ _ : _ ⟶ (Over.pullback (j ≫ A.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ A.hom) ∧
      q ≫ (x3 A 1).left = (snd _ _ : _ ⟶ (Over.pullback (j ≫ A.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ A.hom) := by sorry
