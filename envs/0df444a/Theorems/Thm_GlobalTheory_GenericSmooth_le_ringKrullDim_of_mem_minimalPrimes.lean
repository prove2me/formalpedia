-- Prove2me | Theorems.Thm_GlobalTheory_GenericSmooth_le_ringKrullDim_of_mem_minimalPrimes
-- name    : GlobalTheory.GenericSmooth.le_ringKrullDim_of_mem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:43.158901+00:00
-- url     : https://prove2.me/theorems/48815a57-09e4-4fad-9583-240af08f86a0
-- title:
--   Generic Smooth: le ring Krull Dim of mem minimal Primes
-- statement:
--   The Generic Smooth construction uses the le ring Krull Dim of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothGenericFibreOfIndependentAndTangentBound.lean#L15-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothGenericFibreOfIndependentAndTangentBound.lean#L15-L69

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
open GlobalTheory GlobalTheory.GenericSmooth

theorem GlobalTheory.GenericSmooth.le_ringKrullDim_of_mem_minimalPrimes (o k R S : Type) [CommRing o] [IsDomain o] [Field k]
    [CommRing R] [CommRing S] [Algebra o k] [IsFractionRing o k] [Algebra o R] [Algebra k S]
    [Algebra R S] [Algebra o S] [IsScalarTower o R S] [IsScalarTower o k S]
    [IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors o)) S]
    [Algebra.FiniteType k S] (d : ℕ)
    (h : ∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R →
      (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) : (d : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ q) := by sorry
