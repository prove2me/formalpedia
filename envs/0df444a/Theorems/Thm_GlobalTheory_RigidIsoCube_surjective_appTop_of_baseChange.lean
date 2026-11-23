-- Prove2me | Theorems.Thm_GlobalTheory_RigidIsoCube_surjective_appTop_of_baseChange
-- name    : GlobalTheory.RigidIsoCube.surjective_appTop_of_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:04.676994+00:00
-- url     : https://prove2.me/theorems/b8f08ef2-5068-4cda-a3dd-986f9b5b08f4
-- title:
--   Rigid Iso Cube: surjective app Top of base Change
-- statement:
--   The Rigid Iso Cube construction uses the surjective app Top of base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedIsoRespectsCubeAndSymmetry.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedIsoRespectsCubeAndSymmetry.lean#L14-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedIsoRespectsCubeAndSymmetry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RigidIsoCube

theorem GlobalTheory.RigidIsoCube.surjective_appTop_of_baseChange {Y S Y' S' : Scheme.{0}} {q : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {j : S' ⟶ S}
    (h : IsPullback q p' p j) [Flat p] [QuasiCompact j] [IsSchemeTheoreticallyDominant j] (e : S ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hs : Function.Surjective p'.appTop.hom) : Function.Surjective p.appTop.hom := by sorry
