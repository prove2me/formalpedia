-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_diamond_eigenvalues
-- name    : MazurTransfer.order13_actual_norm_kernel_diamond_eigenvalues
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:09:50.5365+00:00
-- url     : https://prove2.me/theorems/f12ef363-1dc3-4c2c-b6b7-103a898ff051
-- statement:
--   The actual diamond acts on the pi and conjugate norm kernels by eight and twelve; its iterates act by the corresponding powers. This is the conjunction of the three complete original propositions, with all original field and algebraic-closure hypotheses retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
noncomputable section
open scoped CategoryTheory.MonObj
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualNormKernelProductCardinality Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardGeometricDiamondGroupAction Order13ActualPicardSchemeNormGroupHom
open Order13ActualGeometricNineteenTorsionDiamondComparison Order13ActualNineteenTorsionNormPairingAdjoint
attribute [local instance] Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalGroupProvider20261018
  Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalCommProvider20261018
  Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalPiHomProvider20261018
  Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalConjugateHomProvider20261018
  Order13ActualPicardSchemeNormGroupHom.schemeDiamond_isMonHom
  Order13ActualGeometricNineteenTorsionDiamondComparison.nineteenTorsionDiamondOriginalFactProvider20261018
  Order13ActualGeometricNineteenTorsionDiamondComparison.nineteenTorsionDiamondOriginalAlgebraProvider20261018

theorem MazurTransfer.order13_actual_norm_kernel_diamond_eigenvalues :
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : NineteenTorsion K)
    (h : actualNineteenTorsionNormHom K schemePi x = 0),
    actualNineteenTorsionDiamondHom K x = (8 : ℕ) • x) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : NineteenTorsion K)
    (h : actualNineteenTorsionNormHom K schemePiConjugate x = 0),
    actualNineteenTorsionDiamondHom K x = (12 : ℕ) • x) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (n m : ℕ) (x : NineteenTorsion K)
    (h : actualNineteenTorsionDiamondHom K x = m • x),
    ((actualNineteenTorsionDiamondHom K : NineteenTorsion K → NineteenTorsion K)^[n]) x = m ^ n • x) := by sorry
