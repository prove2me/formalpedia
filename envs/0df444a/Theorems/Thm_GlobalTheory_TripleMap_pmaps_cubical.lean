-- Prove2me | Theorems.Thm_GlobalTheory_TripleMap_pmaps_cubical
-- name    : GlobalTheory.TripleMap.pmaps_cubical
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:58:05.127523+00:00
-- url     : https://prove2.me/theorems/2732f6b1-326a-4b26-8ed5-9dc7111332e6
-- title:
--   Triple Map: pmaps cubical
-- statement:
--   The Triple Map construction uses the pmaps cubical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSabMapOfLbIso.lean#L59-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSabMapOfLbIso.lean#L59-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGeometricallyIntegralAbLocusTensorObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfLbIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.TripleMap

theorem GlobalTheory.TripleMap.pmaps_cubical {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w)
    (rigid : ∀ a : Γ((G3 G').left, ⊤)ˣ,
      (∀ y, gm (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left y ⊤ a = 1) →
        a = 1) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by sorry
