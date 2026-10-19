-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDiamondComparison_geometricNineteenTorsionDivisorAddEquiv_diamond
-- name    : MazurTransfer.Order13ActualGeometricNineteenTorsionDiamondComparison.geometricNineteenTorsionDivisorAddEquiv_diamond
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T11:50:18.652113+00:00
-- url     : https://prove2.me/theorems/02b91e6c-53c0-434b-9fb6-321f7bbff52c
-- title:
--   The natural actual nineteen-torsion equivalence intertwines diamond
-- statement:
--   Over every original algebraically closed characteristic-zero field, the same natural additive equivalence from actual Picard nineteen-torsion to arithmetic divisor-class nineteen-torsion commutes with the actual scheme diamond and original arithmetic field diamond actions.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionDiamondComparison.geometricNineteenTorsionDivisorAddEquiv_diamond, exact original theorem and natural torsion equivalence.

import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
noncomputable section
open MazurTransfer
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualGeometricNineteenTorsionDiamondComparison
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] nineteenTorsionDiamondOriginalFactProvider20261018 nineteenTorsionDiamondOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGeometricNineteenTorsionDiamondComparison.geometricNineteenTorsionDivisorAddEquiv_diamond (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (x : NineteenTorsion K) :
    geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionDiamondHom K x) =
      arithmeticNineteenTorsionDiamondHom K (geometricNineteenTorsionDivisorAddEquiv K x) := by sorry
