-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDedekind_exists_isStandardSmoothOfRelativeDimension_of_localization
-- name    : GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_localization
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:13:09.410958+00:00
-- url     : https://prove2.me/theorems/8a992667-fe59-5301-ae88-834401e6e4d4
-- title:
--   Smooth Dedekind: exists is Standard Smooth Of Relative Dimension of localization
-- statement:
--   The Smooth Dedekind construction uses the exists is Standard Smooth Of Relative Dimension of localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L113-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L113-L156

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
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_localization (o V K : Type) [CommRing o]
    [IsNoetherianRing o] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [PerfectField (ResidueField V)] [Field K] [Algebra o V] [Algebra V K] [Algebra o K]
    [IsScalarTower o V K] [IsFractionRing V K] (M : Submonoid o) [IsLocalization M V]
    {A : Type} [CommRing A] [Algebra o A] [Algebra.FiniteType o A] [Module.Flat o A] {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[o] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[o] A) ⧸ p))
    (x : Ideal (ResidueField V ⊗[o] A)) [x.IsMaximal]
    (hx : Module.finrank ((ResidueField V ⊗[o] A) ⧸ x) x.Cotangent ≤ d) :
    ∃ f ∉ x.comap (Algebra.TensorProduct.includeRight : A →ₐ[o] ResidueField V ⊗[o] A).toRingHom,
      Algebra.IsStandardSmoothOfRelativeDimension d o (Localization.Away f) := by sorry
