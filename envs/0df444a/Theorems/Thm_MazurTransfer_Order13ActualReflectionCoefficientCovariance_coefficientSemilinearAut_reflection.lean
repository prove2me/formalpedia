-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualReflectionCoefficientCovariance_coefficientSemilinearAut_reflection
-- name    : MazurTransfer.Order13ActualReflectionCoefficientCovariance.coefficientSemilinearAut_reflection
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:49:31.476984+00:00
-- url     : https://prove2.me/theorems/b327ecd2-fc9d-4b9a-969e-2a7849e7c00a
-- title:
--   The literal reflection is covariant under the coefficient semilinear action
-- statement:
--   Let $K$ be a characteristic-zero field, $\sigma$ a field automorphism of $K$, and $a$ an original reflection parameter. On the same actual curve function field, coefficient transport $c_\sigma$ and reflection $r_a$ satisfy
--   \[c_\sigma r_a=r_{\sigma(a)}c_\sigma.\]
--   The reflection parameter is transported coefficientwise. This is the function-field covariance needed to compare the arithmetic Galois action on Picard nineteen-torsion.
-- source:
--   MazurTheorem Order13ActualReflectionCoefficientCovariance.coefficientSemilinearAut_reflection, retaining the exact original complete universe-polymorphic statement and coefficientFieldMap_reflection helper; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
noncomputable section
universe u
open MazurTransfer AlgebraicCurve
open Order13ReflectionSexticSymmetry Order13ReflectionParameter
open Order13ActualReflectionFunctionField Order13ActualFunctionFieldCoefficientAction
open Order13FieldDiamondFunctionFieldAutomorphism Order13ActualReflectionCoefficientCovariance
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart
attribute [local instance] MazurTransfer.Order13ActualReflectionCoefficientCovariance.reflectionCoefficientOriginalFactProvider20261018
  MazurTransfer.Order13ActualReflectionCoefficientCovariance.reflectionCoefficientOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualReflectionCoefficientCovariance.coefficientSemilinearAut_reflection (K : Type u) [Field K] [CharZero K] (σ : K ≃+* K) (a : ReflectionParameter K) :
    coefficientSemilinearAut K σ * SemilinearAut.ofAlgAut (reflectionAlgEquiv K a) =
      SemilinearAut.ofAlgAut (reflectionAlgEquiv K (mapParameter K σ a)) * coefficientSemilinearAut K σ := by sorry
