-- Prove2me | Theorems.Thm_GlobalTheory_LBLimit_lb_descends_to_fg_subring
-- name    : GlobalTheory.LBLimit.lb_descends_to_fg_subring
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:52:51.123959+00:00
-- url     : https://prove2.me/theorems/9d04b1d5-c2a8-5987-a220-29b7eec9e29e
-- title:
--   LBLimit: lb descends to fg subring
-- statement:
--   The LBLimit construction uses the lb descends to fg subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRefinementOfIsLimit.lean#L225-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRefinementOfIsLimit.lean#L225-L253

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

theorem GlobalTheory.LBLimit.lb_descends_to_fg_subring : ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (L : LB X), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ S : Finset R, ∀ (R₁ : Subring R) (h : R₀ ≤ R₁), (S : Set R) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull j) := by sorry
