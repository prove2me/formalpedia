-- Prove2me | Theorems.Thm_GlobalTheory_TorusExtBaseChange_exists_iso_of_square
-- name    : GlobalTheory.TorusExtBaseChange.exists_iso_of_square
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:26.622543+00:00
-- url     : https://prove2.me/theorems/6451c494-7ce0-4737-b627-1a9f64b1cdbb
-- title:
--   Torus Ext Base Change: exists iso of square
-- statement:
--   The Torus Ext Base Change construction uses the exists iso of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L62-L72

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

theorem GlobalTheory.TorusExtBaseChange.exists_iso_of_square {S S' S₀ S₀' : Scheme.{0}} (f : S' ⟶ S) (f₀ : S₀' ⟶ S₀) (j : S₀ ⟶ S)
    (j' : S₀' ⟶ S') (w : j' ≫ f = f₀ ≫ j) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ e : (Over.pullback j').obj G' ≅ (Over.pullback f₀).obj ((Over.pullback j).obj G), IsMonHom e.hom ∧
      e.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom f₀ ≫ pullback.fst G.hom j =
        pullback.fst G'.hom j' ≫ bc.hom.left ≫ pullback.fst G.hom f := by sorry
