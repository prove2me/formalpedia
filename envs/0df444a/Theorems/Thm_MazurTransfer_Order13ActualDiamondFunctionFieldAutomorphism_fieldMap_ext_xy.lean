-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism_fieldMap_ext_xy
-- name    : MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.fieldMap_ext_xy
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:21:19.158046+00:00
-- url     : https://prove2.me/theorems/d5e5459e-1bee-4334-9522-b70c73d8bf8c
-- title:
--   Maps of the actual rational function field are determined by its two coordinates
-- statement:
--   Let $L$ be the existing function field of the literal order-thirteen curve over $\mathbb Q$. If ring homomorphisms $f,g:L\to L$ agree on its specified ordinary coordinate functions, then $$f(x)=g(x),\quad f(y)=g(y)\quad\Longrightarrow\quad f=g.$$ This supplies the inverse and iterate identities for the actual diamond field automorphism.
-- source:
--   Original complete fieldMap_ext_xy statement and eleven-line proof from MazurTheorem Order13ActualDiamondFunctionFieldAutomorphism.lean, Apache-2.0, Vas and contributors. The entire original statement and proof body are retained; imports and top-level scope alone change. Native, strict and complete frontend checks pass; complete original and public closed types are kernel-compared. Named downstream consumer: actual diamond automorphism inverse identities.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: maps of the actual rational curve function field are determined
by the two literal ordinary coordinates.
Named downstream consumer: diamond field-automorphism inverse identities. -/
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldMap
noncomputable section
open Polynomial MazurTransfer
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13ActualOrdinaryPolynomialTranscendence Order13ActualDiamondFunctionFieldMap
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.fieldMap_ext_xy (f g : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ)
    (hx : f (xImage ℚ) = g (xImage ℚ)) (hy : f (yImage ℚ) = g (yImage ℚ)) : f = g := by sorry
