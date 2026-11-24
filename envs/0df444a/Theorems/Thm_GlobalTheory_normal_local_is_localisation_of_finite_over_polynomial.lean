-- Prove2me | Theorems.Thm_GlobalTheory_normal_local_is_localisation_of_finite_over_polynomial
-- name    : GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:14.432567+00:00
-- url     : https://prove2.me/theorems/42c66bc8-631f-4eac-9193-e0f3110b2282
-- title:
--   Global Theory: normal local is localisation of finite over polynomial
-- statement:
--   The Global Theory construction uses the normal local is localisation of finite over polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormalLocalIsLocalisationOfFiniteOverPolynomialA.lean#L82-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormalLocalIsLocalisationOfFiniteOverPolynomialA.lean#L82-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing

theorem GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B)
      (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by sorry
