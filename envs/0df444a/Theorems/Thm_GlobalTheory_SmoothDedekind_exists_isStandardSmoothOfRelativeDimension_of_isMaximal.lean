-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDedekind_exists_isStandardSmoothOfRelativeDimension_of_isMaximal
-- name    : GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_isMaximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:22.468992+00:00
-- url     : https://prove2.me/theorems/44e2e627-2a5a-4687-98ae-473a4e2371b3
-- title:
--   Smooth Dedekind: exists is Standard Smooth Of Relative Dimension of is Maximal
-- statement:
--   The Smooth Dedekind construction uses the exists is Standard Smooth Of Relative Dimension of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L158-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L158-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing

theorem GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_isMaximal (o : Type) [CommRing o]
    [IsDedekindDomain o] [CharZero o] [Algebra.FiniteType ℤ o]
    {A : Type} [CommRing A] [Algebra o A] [Algebra.FiniteType o A] [Module.Flat o A] {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (FractionRing o ⊗[o] A),
      (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] A) ⧸ p))
    (ht : ∀ (C : Type) [Field C] [IsAlgClosed C] (r : ℕ) (g : A →+* TrivSqZeroExt C (Fin r → C)),
      (∀ c : o, (g (algebraMap o A c)).snd = 0) →
      (∀ lam : (Fin r → C) →ₗ[C] C, (∀ a, lam (g a).snd = 0) → lam = 0) → r ≤ d)
    (q : Ideal A) [q.IsMaximal] :
    ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d o (Localization.Away f) := by sorry
