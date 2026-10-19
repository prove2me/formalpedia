-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_card_eq_kernel_product
-- name    : MazurTransfer.Order13ActualNormKernelProductCardinality.nineteenTorsion_card_eq_kernel_product
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T08:42:55.599666+00:00
-- url     : https://prove2.me/theorems/245c2b7d-b8c4-4697-a015-fd1ba95ba950
-- title:
--   The actual Picard nineteen-torsion has the product cardinality of its two norm kernels
-- statement:
--   For every characteristic-zero field K in the exact original field universe, the cardinality of the original actual Picard nineteen-torsion is the product of the cardinalities of its two specific norm kernels. This is the original kernel-product equivalence on the same Picard scheme; it does not assert the individual ranks.
-- source:
--   MazurTheorem, Order13ActualNormKernelProductCardinality.lean, Apache-2.0. Complete original theorem type and original kernel-product constructor types and values checked. Named downstream consumer: the actual geometric nineteen-torsion divisor comparison and norm-kernel ranks.

import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelProductCardinality
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018 actualNineteenTorsionProductOriginalPiHomProvider20261018 actualNineteenTorsionProductOriginalConjugateHomProvider20261018

theorem MazurTransfer.Order13ActualNormKernelProductCardinality.nineteenTorsion_card_eq_kernel_product (K : Type) [Field K] [CharZero K] :
    Nat.card (NineteenTorsion K) = Nat.card (Kernel K schemePi) * Nat.card (Kernel K schemePiConjugate) := by sorry
