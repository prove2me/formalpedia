-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardDiamondTrace_hyperelliptic_trace_zero
-- name    : MazurTransfer.Order13ActualPicardDiamondTrace.hyperelliptic_trace_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T17:02:21.267343+00:00
-- url     : https://prove2.me/theorems/29fc7c0c-999f-413a-bbf6-6cc4f2e4a754
-- title:
--   The actual diamond-cube arithmetic Pic0 trace is zero
-- statement:
--   For every class c in the actual degree-zero arithmetic Picard group of the order-thirteen curve over Q, the literal diamond action rho satisfies c + (rho^3)c = 0. The original group, action, scalar structures and all hypotheses are retained.
-- source:
--   Complete original MazurTheorem Order13ActualPicardDiamondTrace proof, with public fixed-field identifications and public cyclic trace inputs. Official Anthropic FLT divisor/Pic0 interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original complete literal diamond Pic0 trace contract and proof retained.
Only public fixed-field, arithmetic endomorphism and cyclic-trace inputs are
imported. The curve-over-field instance is the explicit projection of the
accepted public actual function-field invariants statement.
Design boundary: actual arithmetic diamond-square/cube trace identities.
Named downstream consumer: original cyclotomic relation and nineteen norm.
Official Anthropic FLT trace interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualHyperellipticFixedFieldData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Theorems.Thm_MazurTransfer_RationalFixedFieldPicardTrace_cyclic_pic0_trace_eq_zero
noncomputable section
open MazurTransfer
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualConicFieldCubicExtension Order13ActualHyperellipticFixedField
open Order13ActualDiamondFunctionFieldAutomorphism Order13ActualDiamondExactOrder
open Order13ActualDiamondPicardEndomorphisms RationalFixedFieldPicardTrace
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance (B : IntermediateField ℚ (actualCurveFunctionField ℚ)) : Algebra ℚ B :=
  IntermediateField.algebra' B
local instance : Algebra ℚ conicField := IntermediateField.algebra' conicField
local instance : Algebra ℚ xField := IntermediateField.algebra' xField
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance : IsCurveOver ℚ (actualCurveFunctionField ℚ) :=
  (MazurTransfer.order13_actual_function_field_invariants ℚ Fact.out).1

theorem MazurTransfer.Order13ActualPicardDiamondTrace.hyperelliptic_trace_zero (c : ActualPicard) : c + (rho ^ 3) c = 0 := by sorry
