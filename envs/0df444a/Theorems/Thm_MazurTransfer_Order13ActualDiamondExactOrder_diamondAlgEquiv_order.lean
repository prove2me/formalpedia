-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualDiamondExactOrder_diamondAlgEquiv_order
-- name    : MazurTransfer.Order13ActualDiamondExactOrder.diamondAlgEquiv_order
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:54:46.828214+00:00
-- url     : https://prove2.me/theorems/2e6fcd7b-0110-47d9-a9f8-b3dc8903f8d0
-- title:
--   The actual rational diamond field automorphism has exact order six
-- statement:
--   The specified diamond automorphism $\sigma$ of the existing function field of the literal order-thirteen curve over $\mathbb Q$ has exact order $$\operatorname{ord}(\sigma)=6.$$ Its third iterate is the nontrivial hyperelliptic involution and its square is nonidentity on the ordinary coordinate. This exact order supplies the corresponding generic-compatible curve-lift order and Picard descent identities.
-- source:
--   Original complete retained MazurTheorem proof, Apache-2.0, Vas and contributors. The complete original exact-order statement and main proof body are retained. Its six short original coordinate and power helpers are inlined unchanged under a fresh namespace. No exact-order assumption is added. Native, strict and complete frontend checks pass; full original and public closed types are kernel-compared. The design boundary and named downstream consumer are explicit in the source and source-authority manifest.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual function-field automorphism has exact order
six; its cube is a nontrivial hyperelliptic involution. Named downstream
consumer: the actual Picard action used by the nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism

noncomputable section
open MazurTransfer
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13ActualOrdinaryPolynomialTranscendence Order13ActualDiamondFunctionFieldMap
open Order13ActualDiamondFunctionFieldAutomorphism Order13DiamondSexticSymmetry
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : CharZero (actualCurveFunctionField ℚ) := algebraRat.charZero _
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13ActualDiamondExactOrder.diamondAlgEquiv_order : orderOf diamondAlgEquiv = 6 := by sorry
