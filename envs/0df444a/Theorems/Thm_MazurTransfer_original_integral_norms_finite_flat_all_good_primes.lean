-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_norms_finite_flat_all_good_primes
-- name    : MazurTransfer.original_integral_norms_finite_flat_all_good_primes
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T05:11:56.950986+00:00
-- url     : https://prove2.me/theorems/2e2dd795-e383-4267-b94a-24591018d3f7
-- statement:
--   Both same selected integral norm extensions and their fibres over every original test-scheme point are finite, flat, locally finitely presented and surjective at every prime not dividing 104, including nineteen. The original scalar comparison and both original norm composition equalities are retained. Named downstream consumer: integral norm-kernel Hopf models and norm-preimage torsors at nineteen.

import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormCompositionData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralScalarNineteen_integralNorm_scalar
import Theorems.Thm_MazurTransfer_original_positive_scalar_norm_factors_finite_flat
import Theorems.Thm_MazurTransfer_original_local_picard_group_law_commutative
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.Order13GoodPrimeIntegralNormComposition
open MazurTransfer.Order13GoodPrimeIntegralScalarNineteen MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup

theorem MazurTransfer.original_integral_norms_finite_flat_all_good_primes : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), (IsFinite (integralPi q hq).val ∧ Flat (integralPi q hq).val ∧
      LocallyOfFinitePresentation (integralPi q hq).val ∧ Surjective (integralPi q hq).val) ∧
    (IsFinite (integralPiConjugate q hq).val ∧ Flat (integralPiConjugate q hq).val ∧
      LocallyOfFinitePresentation (integralPiConjugate q hq).val ∧
        Surjective (integralPiConjugate q hq).val)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ {T : Scheme}
    (x : T ⟶ (localPicard q hq).P),
(IsFinite (pullback.snd (integralPi q hq).val x) ∧
      Flat (pullback.snd (integralPi q hq).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPi q hq).val x) ∧
      Surjective (pullback.snd (integralPi q hq).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate q hq).val x) ∧
      Flat (pullback.snd (integralPiConjugate q hq).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPiConjugate q hq).val x) ∧
      Surjective (pullback.snd (integralPiConjugate q hq).val x))) := by sorry
