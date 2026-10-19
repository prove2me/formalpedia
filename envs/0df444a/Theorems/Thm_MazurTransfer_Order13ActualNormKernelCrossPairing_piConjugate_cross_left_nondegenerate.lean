-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_piConjugate_cross_left_nondegenerate
-- name    : MazurTransfer.Order13ActualNormKernelCrossPairing.piConjugate_cross_left_nondegenerate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T12:56:22.41041+00:00
-- url     : https://prove2.me/theorems/76090084-9448-4700-a3c2-1a6d862be6fe
-- title:
--   Actual conjugate norm kernel pairs nondegenerately with the opposite norm kernel
-- statement:
--   For the actual divisorial nineteen pairing, an element of the restricted conjugate norm kernel that pairs trivially with every element of the opposite actual norm kernel is zero, over any algebraically closed field of characteristic zero.
-- source:
--   MazurTheorem Order13ActualNormKernelCrossPairing.piConjugate_cross_left_nondegenerate; original complete restricted norm-kernel and actual pairing statement.

import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Order13ActualNormKernelProductCardinality Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualPicardSchemeNineteenNorm Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualNineteenTorsionPairingTransport
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018
attribute [local instance] pairingTransportOriginalFactProvider20261018 pairingTransportOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualNormKernelCrossPairing.piConjugate_cross_left_nondegenerate (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (x : (actualNineteenTorsionNormHom K schemePiConjugate).ker)
    (h : ∀ y : (actualNineteenTorsionNormHom K schemePi).ker,
      actualGeometricNineteenPairing K x.val y.val = 1) : x = 0 := by sorry
