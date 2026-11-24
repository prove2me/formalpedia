-- Prove2me | Theorems.Thm_GlobalTheory_FormalChart_ext_of_isHausdorff
-- name    : GlobalTheory.FormalChart.ext_of_isHausdorff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:34:28.759744+00:00
-- url     : https://prove2.me/theorems/6278be80-8f70-4c3f-91b0-edf88064260f
-- title:
--   Formal Chart: ext of is Hausdorff
-- statement:
--   The Formal Chart construction uses the ext of is Hausdorff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LePreimageOfClosedPoint.lean#L25-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LePreimageOfClosedPoint.lean#L25-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LePreimageOfClosedPoint
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
open GlobalTheory GlobalTheory.FormalChart
variable {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] {g : ℕ}

theorem GlobalTheory.FormalChart.ext_of_isHausdorff (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra O A] (J : Ideal A) [IsHausdorff J A] (φ₁ φ₂ : B →ₐ[O] A)
    (h : ∀ b, φ₁ b - φ₂ b ∈ J)
    (hs : ∀ j : Fin g, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by sorry
