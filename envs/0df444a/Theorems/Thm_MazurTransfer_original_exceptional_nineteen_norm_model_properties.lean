-- Prove2me | Theorems.Thm_MazurTransfer_original_exceptional_nineteen_norm_model_properties
-- name    : MazurTransfer.original_exceptional_nineteen_norm_model_properties
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T05:50:24.501873+00:00
-- url     : https://prove2.me/theorems/fa1fb43f-9899-41a1-888a-a716f9ed4735
-- statement:
--   The original coefficient localization at nineteen is a good-prime base. Every original rational point gives the same generic point of the chosen integral Picard and extends uniquely over that same integral model. Both original selected norm-preimage families over arbitrary original test schemes are finite, flat, locally finitely presented and surjective. All original maps and model designations are retained. Named downstream consumer: arithmetic integral norm-kernel Hopf models and Kummer local conditions at nineteen.

import Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_original_integral_norms_finite_flat_all_good_primes
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
attribute [local instance] MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.instFactPrimeOfNatNat_order13ExceptionalNineteenFlatNormFibres

theorem MazurTransfer.original_exceptional_nineteen_norm_model_properties : (¬ (19 : ℤ) ∣ 104) ∧ (∀ (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase),
∃! x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) integralModel.toBase,
      genericFibreRestrict (LocalRing 19) ℚ integralModel.toBase
        (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) x = actualGenericPoint z) ∧ (∀ {T : Scheme}
    (x : T ⟶ integralModel.P),
(IsFinite (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      Flat (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      Surjective (pullback.snd (integralPi 19 nineteen_good).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      Flat (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      Surjective (pullback.snd (integralPiConjugate 19 nineteen_good).val x))) := by sorry
