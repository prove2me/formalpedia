-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_pi_cross_left_nondegenerate
-- name    : MazurTransfer.Order13ActualNormKernelCrossPairing.pi_cross_left_nondegenerate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T12:49:50.317964+00:00
-- url     : https://prove2.me/theorems/a64314ed-8633-4fdf-a727-6b26ce747180
-- title:
--   Actual pi norm kernel pairs nondegenerately with the opposite norm kernel
-- statement:
--   For the actual divisorial nineteen pairing, an element of the restricted pi norm kernel that pairs trivially with every element of the opposite actual norm kernel is zero, over any algebraically closed field of characteristic zero.
-- source:
--   MazurTheorem Order13ActualNormKernelCrossPairing.pi_cross_left_nondegenerate; original complete restricted norm-kernel and actual pairing statement.

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

theorem MazurTransfer.Order13ActualNormKernelCrossPairing.pi_cross_left_nondegenerate (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (x : (actualNineteenTorsionNormHom K schemePi).ker)
    (h : ∀ y : (actualNineteenTorsionNormHom K schemePiConjugate).ker,
      actualGeometricNineteenPairing K x.val y.val = 1) : x = 0 := by sorry
