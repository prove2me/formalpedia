-- Prove2me | Theorems.Thm_GlobalTheory_RigidIsoCube_surjective_snd_of_generic
-- name    : GlobalTheory.RigidIsoCube.surjective_snd_of_generic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:11.714778+00:00
-- url     : https://prove2.me/theorems/e52cb25e-abd3-4ac7-9ba4-d3da73001c1e
-- title:
--   Rigid Iso Cube: surjective snd of generic
-- statement:
--   The Rigid Iso Cube construction uses the surjective snd of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedIsoRespectsCubeAndSymmetry.lean#L35-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RigidifiedIsoRespectsCubeAndSymmetry.lean#L35-L52

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

theorem GlobalTheory.RigidIsoCube.surjective_snd_of_generic (hG : GlobalFnsSt) {S S' : Scheme.{0}} (k : S' ⟶ S) [QuasiCompact k]
    [IsSchemeTheoreticallyDominant k] (G : Over S) [GrpObj G] [Flat G.hom] {A : Over S'} [GrpObj A]
    (hA : IsAbelianScheme A) {g : A.left ⟶ G.left} (hg : IsPullback g A.hom G.hom k) (T : Over S) [Flat T.hom] :
    Function.Surjective (snd G T).left.appTop.hom := by sorry
