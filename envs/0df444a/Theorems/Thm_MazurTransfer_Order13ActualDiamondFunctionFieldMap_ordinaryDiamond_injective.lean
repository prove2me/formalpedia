-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualDiamondFunctionFieldMap_ordinaryDiamond_injective
-- name    : MazurTransfer.Order13ActualDiamondFunctionFieldMap.ordinaryDiamond_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:13:38.567927+00:00
-- url     : https://prove2.me/theorems/34ee2183-e043-4f3e-a80e-879bc144d07b
-- title:
--   The actual ordinary diamond coordinate homomorphism is injective
-- statement:
--   For the literal order-thirteen curve over $\mathbb Q$, the specified diamond coordinate homomorphism from its actual ordinary coordinate algebra to its existing scheme function field, given on coordinates by $$x\longmapsto-\frac1{x+1},\qquad y\longmapsto\frac{y}{(x+1)^3},$$ is injective. This is the injection needed to extend the actual substitution to the fraction field.
-- source:
--   Original complete ordinaryDiamond_injective statement and proof from MazurTheorem Order13ActualDiamondFunctionFieldMap.lean, Apache-2.0, Vas and contributors. The entire original statement is retained. The main proof body changes only the namespace qualification of the four-line original integral-ring-map helper, inlined under a fresh namespace. Uses the Proved public diamond-coordinate transcendence theorem and the original actual coordinate-map data and polynomial-integrality interface. Native, strict and complete frontend checks pass; complete original/public types are kernel-compared. Named downstream consumer: actual rational diamond field endomorphism.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the actual diamond coordinate homomorphism is injective.
Named downstream consumer: extension to the literal rational function field. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryDiamondCoordinateMap
noncomputable section
open MazurTransfer.Order13ActualDiamondFunctionFieldMap

theorem MazurTransfer.Order13ActualDiamondFunctionFieldMap.ordinaryDiamond_injective : Function.Injective ordinaryDiamond := by sorry
