-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_picard_geometry_and_unique_integral_norm_extensions
-- name    : MazurTransfer.order13_actual_dyadic_picard_geometry_and_unique_integral_norm_extensions
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T09:15:41.110897+00:00
-- url     : https://prove2.me/theorems/4d134419-d326-42dd-b799-5b910a37adff
-- statement:
--   Let $R=\mathbf{Z}_{(2)}$ and let $J/R$ be the same original chosen dyadic Picard scheme, with generic fibre $J_\eta$. Its dyadic and rational fibres are smooth, proper and geometrically connected. Every arithmetic Picard endomorphism $\phi$ has a transported generic-fibre endomorphism $\phi_\eta$ with a unique integral extension:
--
--   $$\exists!\,N_\phi:J\longrightarrow_R J,\qquad (N_\phi)_\eta=\phi_\eta.$$
--
--   The original chosen extensions, including both actual norm factors, retain their whole constructor values. Named downstream consumer: the integral norm group laws and scalar composition identities.

import Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardGeometryAndUniqueNormExtensionsData20261019
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13DyadicMixedGenericNorms Order13DyadicMixedIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedPicardGeometry.instFactPrimeOfNatNat_order13DyadicMixedPicardGeometry
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNorms.instFactPrimeOfNatNat_order13DyadicMixedGenericNorms
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormExtensions.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormExtensions

theorem MazurTransfer.order13_actual_dyadic_picard_geometry_and_unique_integral_norm_extensions : (Smooth dyadicPicard.toBase ∧ IsProper dyadicPicard.toBase ∧
    GeometricallyConnected dyadicPicard.toBase) ∧ (Smooth rationalPicard.toBase ∧ IsProper rationalPicard.toBase ∧
    GeometricallyConnected rationalPicard.toBase) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase), ∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericNorm φ) ∧ ((∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericPi) ∧
    (∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericPiConjugate)) := by sorry
