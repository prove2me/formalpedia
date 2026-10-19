-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDivisorComparison_geometricTorsionClassHom_injective
-- name    : MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T11:01:36.571273+00:00
-- url     : https://prove2.me/theorems/96bfc97a-684b-4622-907c-c408e61bbc93
-- title:
--   The natural actual Picard nineteen-torsion divisor-class map is injective
-- statement:
--   Over every original algebraically closed characteristic-zero field, the natural divisor-class map on actual Picard nineteen-torsion is injective. The source, target, scalar constructions and natural map are the original ones used for transport of the actual Weil pairing.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_injective, exact original contract.

import Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
noncomputable section
open MazurTransfer
open Order13ActualGeometricNineteenTorsionDivisorComparison
attribute [local instance] naturalDivisorMapOriginalFactProvider20261018 naturalDivisorMapOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_injective (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Function.Injective (geometricTorsionClassHom K) := by sorry
