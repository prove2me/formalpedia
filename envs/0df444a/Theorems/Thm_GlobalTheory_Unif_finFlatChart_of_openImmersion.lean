-- Prove2me | Theorems.Thm_GlobalTheory_Unif_finFlatChart_of_openImmersion
-- name    : GlobalTheory.Unif.finFlatChart_of_openImmersion
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:47.805885+00:00
-- url     : https://prove2.me/theorems/5a6a408f-5297-4d05-8816-a4c482750809
-- title:
--   Unif: fin Flat Chart of open Immersion
-- statement:
--   The Unif construction uses the fin Flat Chart of open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FinFlatChartOfOpenImmersion.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FinFlatChartOfOpenImmersion.lean#L17-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinFlatChartOfOpenImmersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
open GlobalTheory GlobalTheory.Unif

theorem GlobalTheory.Unif.finFlatChart_of_openImmersion {X Y Z S B : Scheme.{0}} (f : X ⟶ B) (s : S ⟶ B)
    (j : Y ⟶ X) [IsOpenImmersion j] (i : Z ⟶ S) [IsOpenImmersion i] (p : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [Nonempty Z] (h : p ≫ i ≫ s = j ≫ f) :
    ∃ (W : X.Opens) (V : S.Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧
      IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ s = W.ι ≫ f := by sorry
