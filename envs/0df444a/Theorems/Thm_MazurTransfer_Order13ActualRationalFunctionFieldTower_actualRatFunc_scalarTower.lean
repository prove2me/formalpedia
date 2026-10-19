-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualRationalFunctionFieldTower_actualRatFunc_scalarTower
-- name    : MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFunc_scalarTower
-- status  : Open
-- author  : @Vas
-- created : 2026-10-18T08:01:39.334697+00:00
-- url     : https://prove2.me/theorems/85932d4f-1d65-4cc3-ac4c-8eb52c88df81
-- title:
--   The original actual order-13 RatFunc embedding forms a scalar tower
-- statement:
--   For every field K of characteristic zero, the original base-field algebra of the actual order-13 curve function field and the original RatFunc K algebra induced by its x-coordinate embedding form an IsScalarTower K (RatFunc K) (actualCurveFunctionField K).
-- source:
--   MazurTheorem, Order13ActualRationalFunctionFieldTower.lean; Apache-2.0. Original complete telescope, algebra definitions, and original source/dependency instance types and nonproof values checked. Named consumer: injectivity of the actual divisorial nineteen-pairing.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual order-13 function field is finite over the
rational function field via its existing transcendental x-coordinate.
Named downstream consumer: instantiate the divisibility-based injectivity
theorem for the actual divisorial nineteen-pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
noncomputable section
open MazurTransfer
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13FieldHyperellipticFixedField Order13ActualRationalFunctionFieldTower
attribute [local instance] actualRatFuncTowerOriginalFactProvider20261018 actualRatFuncTowerOriginalAlgebraProvider20261018
local instance scalarTowerOriginalRatFuncAlgebraProvider20261018 (K : Type*) [Field K] [CharZero K] : Algebra (RatFunc K) (actualCurveFunctionField K) := actualRatFuncAlgebra K

theorem MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFunc_scalarTower (K : Type*) [Field K] [CharZero K] : IsScalarTower K (RatFunc K) (actualCurveFunctionField K) := by sorry
