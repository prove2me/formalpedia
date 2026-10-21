-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_norm_unit_and_all_point_identities
-- name    : MazurTransfer.original_integral_norm_unit_and_all_point_identities
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T05:22:34.6496+00:00
-- url     : https://prove2.me/theorems/7043d732-c7c3-48b6-aced-6f1bf6e4ed11
-- statement:
--   The original generic inclusion is dominant, and the same chosen integral extension of every original monoid endomorphism preserves the identity both over the base identity map and on points over every original integral test scheme. The original local Picard law, maps, prime and coefficient hypotheses are retained. Named downstream consumer: actual integral norm-kernel Hopf group laws.

import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormUnit_localGenericNorm_preserves_unit
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open MazurTransfer.Order13GoodPrimeGenericNormUnit MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup

theorem MazurTransfer.original_integral_norm_unit_and_all_point_identities : (∀ (q : ℕ) [Fact q.Prime] , IsDominant (specGenericFibreInclusion (LocalRing q) ℚ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) , ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ],
NeronModelInfra.schemeHomOverComp ((localLaw q hq).one (𝟙 _))
      (integralNorm q hq φ) = (localLaw q hq).one (𝟙 _)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) , ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q))),
NeronModelInfra.schemeHomOverComp ((localLaw q hq).one t) (integralNorm q hq φ) =
      (localLaw q hq).one t) := by sorry
