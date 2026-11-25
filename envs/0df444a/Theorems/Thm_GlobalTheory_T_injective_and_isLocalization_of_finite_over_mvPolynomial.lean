-- Prove2me | Theorems.Thm_GlobalTheory_T_injective_and_isLocalization_of_finite_over_mvPolynomial
-- name    : GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:30.556899+00:00
-- url     : https://prove2.me/theorems/8a973f7f-e020-40ed-9f8d-75bb2ad19523
-- title:
--   T: injective and is Localization of finite over mv Polynomial
-- statement:
--   The T construction uses the injective and is Localization of finite over mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B) (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime), Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by sorry
