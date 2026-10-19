-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDivisorComparison_geometricTorsionClassHom_surjective
-- name    : MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T10:57:05.514141+00:00
-- url     : https://prove2.me/theorems/04046e95-e682-4474-b7bb-c0b908bd29a6
-- title:
--   The natural actual Picard nineteen-torsion divisor-class map is surjective
-- statement:
--   For every algebraically closed characteristic-zero field in the original universe, every arithmetic degree-zero divisor class killed by nineteen is the image of an actual nineteen-torsion point under the original natural geometric divisor-class map. The designated rational Picard and the natural map are the same original constructions.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_surjective; exact original contract, using an auxiliary arithmetic comparison only inside the proof.

import Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
noncomputable section
open MazurTransfer
open Order13ActualGeometricNineteenTorsionDivisorComparison
attribute [local instance] naturalDivisorMapOriginalFactProvider20261018 naturalDivisorMapOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_surjective (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Function.Surjective (geometricTorsionClassHom K) := by sorry
