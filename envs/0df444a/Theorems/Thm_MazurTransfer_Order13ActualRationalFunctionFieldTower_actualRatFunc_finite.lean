-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualRationalFunctionFieldTower_actualRatFunc_finite
-- name    : MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFunc_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T08:15:39.410468+00:00
-- url     : https://prove2.me/theorems/edf094bc-1269-40f0-8661-59d3b1781b48
-- title:
--   The original actual order-13 function field is finite over RatFunc K
-- statement:
--   For every field K of characteristic zero, the actual order-13 curve function field is finite-dimensional over RatFunc K using the original embedding through the existing equivalence RatFunc K ≃ K(x), with its original induced algebra.
-- source:
--   MazurTheorem, Order13ActualRationalFunctionFieldTower.lean; Apache-2.0. Original complete telescope, algebra definitions, and original source/dependency instance types and nonproof values checked. Named consumer: injectivity of the actual divisorial nineteen-pairing.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual order-13 function field is finite over the
rational function field via its existing transcendental x-coordinate.
Named downstream consumer: instantiate the divisibility-based injectivity
result for the actual divisorial nineteen-pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
noncomputable section
open MazurTransfer
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13FieldHyperellipticFixedField Order13ActualRationalFunctionFieldTower
attribute [local instance] actualRatFuncTowerOriginalFactProvider20261018 actualRatFuncTowerOriginalAlgebraProvider20261018

attribute [local instance] actualRatFuncAlgebra

theorem MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFunc_finite (K : Type*) [Field K] [CharZero K] : FiniteDimensional (RatFunc K) (actualCurveFunctionField K) := by sorry
