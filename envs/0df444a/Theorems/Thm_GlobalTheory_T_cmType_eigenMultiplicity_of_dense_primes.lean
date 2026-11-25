-- Prove2me | Theorems.Thm_GlobalTheory_T_cmType_eigenMultiplicity_of_dense_primes
-- name    : GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:39.566572+00:00
-- url     : https://prove2.me/theorems/439c128d-f77e-593d-bb87-1bba45d65c91
-- title:
--   T: cm Type eigen Multiplicity of dense primes
-- statement:
--   The T construction uses the cm Type eigen Multiplicity of dense primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmTypeEigenMultiplicityOfDensePrimesStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmTypeEigenMultiplicityOfDensePrimesStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R] (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) → Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧ (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) → ∀ τ : 𝓞 E →+* K, (τ H.rt = f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧ (τ H.rt ≠ f r → Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by sorry
