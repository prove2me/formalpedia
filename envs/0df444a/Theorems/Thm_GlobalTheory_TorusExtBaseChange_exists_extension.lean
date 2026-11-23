-- Prove2me | Theorems.Thm_GlobalTheory_TorusExtBaseChange_exists_extension
-- name    : GlobalTheory.TorusExtBaseChange.exists_extension
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:17.528554+00:00
-- url     : https://prove2.me/theorems/dbf60f72-f527-4efb-b3ea-abdb5949be36
-- title:
--   Torus Ext Base Change: exists extension
-- statement:
--   The Torus Ext Base Change construction uses the exists extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L28-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L28-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusExtBaseChange

theorem GlobalTheory.TorusExtBaseChange.exists_extension {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    {T' G' B' : Over S'} [GrpObj T'] [GrpObj G'] [GrpObj B']
    (eT : T' ≅ (Over.pullback f).obj T) (eG : G' ≅ (Over.pullback f).obj G)
    (eB : B' ≅ (Over.pullback f).obj B) [IsMonHom eT.hom] [IsMonHom eG.hom] [IsMonHom eB.hom]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] (hf : Flat q.left) (hs : Surjective q.left)
    (ha : IsAffineHom q.left) (hk : IsPullback i (toUnit _) q η[B]) :
    ∃ (q' : G' ⟶ B') (i' : T' ⟶ G'), IsMonHom q' ∧ Flat q'.left ∧ Surjective q'.left ∧
      IsAffineHom q'.left ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' η[B'] ∧
      q'.left ≫ eB.hom.left ≫ pullback.fst B.hom f = (eG.hom.left ≫ pullback.fst G.hom f) ≫ q.left ∧
      i'.left ≫ eG.hom.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst T.hom f) ≫ i.left := by sorry
