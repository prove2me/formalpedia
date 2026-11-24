-- Prove2me | Theorems.Thm_GlobalTheory_T_pullbackSections_basis_affine_baseChange_of_affine
-- name    : GlobalTheory.T.pullbackSections_basis_affine_baseChange_of_affine
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:55:14.121196+00:00
-- url     : https://prove2.me/theorems/bad8c2f2-44ef-454f-b476-625959a6aa2d
-- title:
--   T: pullback Sections basis affine base Change of affine
-- statement:
--   The T construction uses the pullback Sections basis affine base Change of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PullbackSectionsBasisAffineBaseChangeOfAffineStatement.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PullbackSectionsBasisAffineBaseChangeOfAffineStatement.lean#L19-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisAffineBaseChangeOfAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisAffineBaseChangeOfAffineStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pullbackSections_basis_affine_baseChange_of_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), (∀ (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (Y : Scheme.{0}) (p₁ : Y ⟶ Sp R') (p₂ : Y ⟶ X), IsPullback p₂ p₁ p (spMap f) ∧ GlobalTheory.RelBasis.IndepOn b p₁ p₂ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ ⊤) → ∀ (T Y : Scheme.{0}) (q : T ⟶ Sp R) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), IsPullback p₂ p₁ p q → ∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by sorry
