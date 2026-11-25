-- Prove2me | Theorems.Thm_GlobalTheory_TorusExtBaseChange_exists_splitTorus_iso
-- name    : GlobalTheory.TorusExtBaseChange.exists_splitTorus_iso
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:44.085257+00:00
-- url     : https://prove2.me/theorems/3e6fdb20-8025-45e9-95e9-10455cac324f
-- title:
--   Torus Ext Base Change: exists split Torus iso
-- statement:
--   The Torus Ext Base Change construction uses the exists split Torus iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsPullbackPullbackMap.lean#L74-L92

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

theorem GlobalTheory.TorusExtBaseChange.exists_splitTorus_iso {S S' : Scheme.{0}} (f : S' ⟶ S) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (xe : X' ≃+ X) :
    ∃ e : splitTorus S' X' ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ x : X', (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X (xe x)).val =
        (charUnit S' X' x).val := by sorry
