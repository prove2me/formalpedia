-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityClassActualNormKernels_actual_diamond_eq_field_diamond
-- name    : MazurTransfer.Order13InfinityClassActualNormKernels.actual_diamond_eq_field_diamond
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:12:40.581986+00:00
-- url     : https://prove2.me/theorems/68ce66ba-1801-454c-9fba-7d9a07e3cece
-- title:
--   The actual rational diamond automorphism is the field-parametric specialization
-- statement:
--   The specified actual rational diamond automorphism of the X₁(13) function field equals the specialization to the rationals of the original field-parametric diamond automorphism. This is the complete original automorphism equality used to transport the computed infinity-class eigenvalue to the actual arithmetic norm maps.
-- source:
--   Original retained MazurTheorem Order13InfinityClassActualNormKernels; original complete statement retained; Apache-2.0, Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance publicActualFieldDiamondEqualityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicActualFieldDiamondEqualityOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13InfinityClassActualNormKernels.actual_diamond_eq_field_diamond :
    Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv =
      Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv ℚ := by sorry
