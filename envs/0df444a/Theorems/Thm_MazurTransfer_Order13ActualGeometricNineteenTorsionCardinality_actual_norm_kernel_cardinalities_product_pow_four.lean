-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actual_norm_kernel_cardinalities_product_pow_four
-- name    : MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_norm_kernel_cardinalities_product_pow_four
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T10:44:34.836281+00:00
-- url     : https://prove2.me/theorems/4ff26a26-f6e5-4f6f-8333-8b1fdd57214f
-- title:
--   The actual norm-kernel cardinalities multiply to nineteen to the fourth power
-- statement:
--   Over every original algebraically closed characteristic-zero field, the cardinalities of the two actual norm kernels on the designated rational Picard multiply to 19^4. Both kernels are those of the original actual norm endomorphisms. This statement determines their product without asserting either individual rank.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionCardinality.actual_norm_kernel_cardinalities_product_pow_four, exact original theorem and actual norm maps.

import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelProductCardinality
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018 actualNineteenTorsionProductOriginalPiHomProvider20261018 actualNineteenTorsionProductOriginalConjugateHomProvider20261018

theorem MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_norm_kernel_cardinalities_product_pow_four (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Nat.card (Kernel K schemePi) * Nat.card (Kernel K schemePiConjugate) = 19 ^ 4 := by sorry
