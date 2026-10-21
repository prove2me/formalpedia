-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_norm_multiplication
-- name    : MazurTransfer.original_integral_norm_multiplication
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T05:39:16.639732+00:00
-- url     : https://prove2.me/theorems/b357a981-7036-4f29-b676-19b9c2be4a49
-- statement:
--   The same chosen integral extension of every original rational Picard monoid endomorphism preserves multiplication for the same local Picard law on every original integral test scheme. The original prime, coefficient, endomorphism, group-law and point hypotheses are retained. Named downstream consumer: actual integral norm-kernel Hopf group laws and finite-flat arithmetic quotients.

import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_localGenericNorm_preserves_mul
import Theorems.Thm_MazurTransfer_original_relative_group_law_generic_fibre_multiplication_descent
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalGenericGroupIdentity MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison
open MazurTransfer.Order13GoodPrimeGenericNormGroupLaws MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup

theorem MazurTransfer.original_integral_norm_multiplication : ∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (LocalRing q)))
    (x y : SchemeHomOver t (localPicard q hq).toBase),
NeronModelInfra.schemeHomOverComp ((localLaw q hq).mul t x y) (integralNorm q hq φ) =
    (localLaw q hq).mul t
      (NeronModelInfra.schemeHomOverComp x (integralNorm q hq φ))
      (NeronModelInfra.schemeHomOverComp y (integralNorm q hq φ)) := by sorry
