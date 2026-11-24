-- Prove2me | Theorems.Thm_GlobalTheory_eigenMult_of_dense
-- name    : GlobalTheory.eigenMult_of_dense
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:07.410289+00:00
-- url     : https://prove2.me/theorems/a29cb7c7-e320-4a5b-8156-88832ed47aa8
-- title:
--   Global Theory: eigen Mult of dense
-- statement:
--   The Global Theory construction uses the eigen Mult of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmTypeEigenMultiplicityOfDensePrimes.lean#L213-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmTypeEigenMultiplicityOfDensePrimes.lean#L213-L263

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.eigenMult_of_dense : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R]
    (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) →
    Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K)
      (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧
      (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K,
        (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
        (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q)} →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K)
      (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) →
      ∀ τ : 𝓞 E →+* K,
        (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
        (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by sorry
