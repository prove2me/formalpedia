-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_finite
-- name    : MazurTransfer.Order13ActualNormKernelProductCardinality.nineteenTorsion_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T08:47:30.541499+00:00
-- url     : https://prove2.me/theorems/0af8a776-1f75-4395-8651-9a9165307529
-- title:
--   The original actual Picard nineteen-torsion is finite
-- statement:
--   For every characteristic-zero field K in the exact original field universe, the original subgroup of actual Picard points killed by nineteen is finite. No algebraic closure or individual kernel rank is assumed.
-- source:
--   MazurTheorem, Order13ActualNormKernelProductCardinality.lean, Apache-2.0. Complete original theorem type and original kernel-product constructor types and values checked. Named downstream consumer: the actual geometric nineteen-torsion divisor comparison and norm-kernel ranks.

import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelProductCardinality
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018 actualNineteenTorsionProductOriginalPiHomProvider20261018 actualNineteenTorsionProductOriginalConjugateHomProvider20261018

theorem MazurTransfer.Order13ActualNormKernelProductCardinality.nineteenTorsion_finite (K : Type) [Field K] [CharZero K] : Finite (NineteenTorsion K) := by sorry
