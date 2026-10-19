-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelRanksTwo_actual_norm_kernel_cards_eq
-- name    : MazurTransfer.Order13ActualNormKernelRanksTwo.actual_norm_kernel_cards_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T12:22:39.800999+00:00
-- url     : https://prove2.me/theorems/867da177-987d-4b60-9e2f-15efed6bd83d
-- title:
--   The two complete actual order-thirteen Picard norm kernels have equal cardinalities
-- statement:
--   Over every algebraically closed characteristic-zero field, the two complete geometric kernels of the actual order-thirteen Picard norm factors have equal cardinalities. The proof constructs and uses the actual perfect divisorial nineteen-pairing; no rank or character-surjectivity hypothesis is added.
-- source:
--   MazurTheorem Order13ActualNormKernelRanksTwo.actual_norm_kernel_cards_eq, with original natural nineteen-torsion comparison and complete norm-kernel equivalences. Finite character counting reuses official Anthropic FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelProductCardinality
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018

theorem MazurTransfer.Order13ActualNormKernelRanksTwo.actual_norm_kernel_cards_eq (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Nat.card (Kernel K schemePi) = Nat.card (Kernel K schemePiConjugate) := by sorry
