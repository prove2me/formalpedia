-- Prove2me | Theorems.Thm_GlobalTheory_smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le
-- name    : GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:04:59.961455+00:00
-- url     : https://prove2.me/theorems/99587b0c-d5b8-4508-93e7-0808e2ccca6f
-- title:
--   Global Theory: smooth Of Relative Dimension generic Fibre of independent of finrank derivation le
-- statement:
--   The Global Theory construction uses the smooth Of Relative Dimension generic Fibre of independent of finrank derivation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothGenericFibreOfIndependentAndTangentBound.lean#L101-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothGenericFibreOfIndependentAndTangentBound.lean#L101-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGenericFibreOfIndependentAndTangentBound
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
open GlobalTheory
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le :
    ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by sorry
