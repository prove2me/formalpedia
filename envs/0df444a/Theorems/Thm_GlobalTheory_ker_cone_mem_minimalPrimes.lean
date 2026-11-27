-- Prove2me | Theorems.Thm_GlobalTheory_ker_cone_mem_minimalPrimes
-- name    : GlobalTheory.ker_cone_mem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:48.716384+00:00
-- url     : https://prove2.me/theorems/a87463e9-51e8-574e-b849-18fbf101c775
-- title:
--   Global Theory: ker cone mem minimal Primes
-- statement:
--   The Global Theory construction uses the ker cone mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KerConeMemMinimalPrimes.lean#L70-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KerConeMemMinimalPrimes.lean#L70-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KerConeMemMinimalPrimes
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
open GlobalTheory
open HomogMinPrime

theorem GlobalTheory.ker_cone_mem_minimalPrimes : ∀ (o σ K : Type) [CommRing o] [Field K] (I : Ideal (MvPolynomial σ o)) (β : o →+* K) (u : σ → K) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → u i = 1 → RingHom.ker (MvPolynomial.eval₂Hom β u) ∈ (I ⊔ Ideal.span {MvPolynomial.X i - 1}).minimalPrimes → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) ∈ I.minimalPrimes := by sorry
