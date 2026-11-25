-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDedekind_smoothOfRelativeDimension_of_flat_of_tangent_le
-- name    : GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:49.657196+00:00
-- url     : https://prove2.me/theorems/d8e88206-935a-46be-a799-27c39c9d3ae7
-- title:
--   Smooth Dedekind: smooth Of Relative Dimension of flat of tangent le
-- statement:
--   The Smooth Dedekind construction uses the smooth Of Relative Dimension of flat of tangent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L214-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L214-L259

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

theorem GlobalTheory.SmoothDedekind.smoothOfRelativeDimension_of_flat_of_tangent_le : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] [CharZero o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), Algebra.FiniteType ℤ o → Flat s → LocallyOfFiniteType s → (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : o →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X), x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) → (∀ lam : (Fin r → K) →ₗ[K] K, spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) → SmoothOfRelativeDimension d s := by sorry
