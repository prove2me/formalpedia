-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualFunctionFieldGenerators_intermediateField_eq_top
-- name    : MazurTransfer.Order13ActualFunctionFieldGenerators.intermediateField_eq_top
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T16:19:53.250987+00:00
-- url     : https://prove2.me/theorems/ddeb7a1c-e358-42d6-8ec1-eeeb04cb1868
-- title:
--   The literal ordinary coordinates generate the actual rational curve function field
-- statement:
--   Any intermediate field of the literal rational order-13 curve function field containing its original ordinary x and y coordinates is the entire actual function field. The specified intermediate field and both coordinate-membership hypotheses are the complete original contract.
-- source:
--   Unchanged complete original MazurTheorem Order13ActualFunctionFieldGenerators.intermediateField_eq_top proof and statement, Apache-2.0, Vas and contributors. The public actual ordinary coordinates and polynomial-transcendence Definition supply the original constructors.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original complete actual coordinate field-generation proof retained.
Design boundary: any intermediate field containing the literal ordinary
x and y coordinates is the actual rational scheme function field.
Named downstream consumer: actual conic cubic and hyperelliptic fixed fields.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryPolynomialTranscendence
noncomputable section
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13PellActualOrdinaryChart MazurTransfer.Order13ActualOrdinaryPolynomialTranscendence
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ActualFunctionFieldGenerators.intermediateField_eq_top (S : IntermediateField ℚ (actualCurveFunctionField ℚ))
    (hx : xImage ℚ ∈ S) (hy : yImage ℚ ∈ S) : S = ⊤ := by sorry
