-- Prove2me | Theorems.Thm_GlobalTheory_morphism_descends_to_subring
-- name    : GlobalTheory.morphism_descends_to_subring
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:10.062978+00:00
-- url     : https://prove2.me/theorems/eb95ea51-c434-4e82-8df8-10652cf3391e
-- title:
--   Global Theory: morphism descends to subring
-- statement:
--   The Global Theory construction uses the morphism descends to subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MorphismDescendsToSubring.lean#L26-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MorphismDescendsToSubring.lean#L26-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MorphismDescendsToSubring
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
open GlobalTheory

theorem GlobalTheory.morphism_descends_to_subring :
    ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X X₀ Y₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp R₀) (q : Y₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation q] (φ : X ⟶ Y₀), IsPullback π f f₀ (spMap R₀.subtype) → φ ≫ q = π ≫ f₀ → ∃ S : Finset R, ∀ (R₁ : Subring R) (h : R₀ ≤ R₁), (S : Set R) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Y₀, j ≫ ψ = φ ∧ ψ ≫ q = π₁ ≫ f₀ := by sorry
