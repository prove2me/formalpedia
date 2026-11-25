-- Prove2me | Theorems.Thm_GlobalTheory_LBLimit_exists_refinement_of_isLimit
-- name    : GlobalTheory.LBLimit.exists_refinement_of_isLimit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:26.827696+00:00
-- url     : https://prove2.me/theorems/4c6782ae-c034-4ae1-bde7-9b221bf069ba
-- title:
--   LBLimit: exists refinement of is Limit
-- statement:
--   The LBLimit construction uses the exists refinement of is Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRefinementOfIsLimit.lean#L113-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRefinementOfIsLimit.lean#L113-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRefinementOfIsLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.LBLimit
variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, QuasiSeparatedSpace (D.obj i)]
include hc

theorem GlobalTheory.LBLimit.exists_refinement_of_isLimit [∀ i, CompactSpace (D.obj i)] (L : LB X) (hL : L.IsLB) :
    ∃ (j : I) (M : LB (D.obj j)) (e : M.ι → L.ι), M.IsLB ∧ (∀ a, π j ⁻¹ᵁ M.U a ≤ L.U (e a)) ∧
      ∀ a b (y : X), π j y ∈ M.U a → π j y ∈ M.U b →
        gm (π j) y _ (M.g a b) = gm (𝟙 X) y _ (L.g (e a) (e b)) := by sorry
