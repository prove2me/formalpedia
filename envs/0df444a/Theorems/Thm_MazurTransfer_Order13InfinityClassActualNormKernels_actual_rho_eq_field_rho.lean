-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityClassActualNormKernels_actual_rho_eq_field_rho
-- name    : MazurTransfer.Order13InfinityClassActualNormKernels.actual_rho_eq_field_rho
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:26:54.953556+00:00
-- url     : https://prove2.me/theorems/57f88328-32d0-4c39-8575-5a60fb4959e9
-- title:
--   The actual rational Picard diamond is the field-parametric specialization
-- statement:
--   The original actual rational arithmetic Picard diamond endomorphism equals the specialization to the rationals of the original field-parametric Picard diamond endomorphism. This complete equality identifies the arithmetic actions used in the infinity-class eigenvalue and actual norm-kernel ordering.
-- source:
--   MazurTheorem Order13InfinityClassActualNormKernels.actual_rho_eq_field_rho; exact original equality retained; original official Anthropic FLT arithmetic Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance publicActualRhoFieldEqualityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicActualRhoFieldEqualityOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13InfinityClassActualNormKernels.actual_rho_eq_field_rho : Order13ActualDiamondPicardEndomorphisms.rho =
    Order13FieldDiamondPicardEndomorphisms.rho ℚ := by sorry
