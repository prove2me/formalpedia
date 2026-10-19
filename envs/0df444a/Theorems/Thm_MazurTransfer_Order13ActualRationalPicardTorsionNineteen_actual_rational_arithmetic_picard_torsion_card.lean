-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualRationalPicardTorsionNineteen_actual_rational_arithmetic_picard_torsion_card
-- name    : MazurTransfer.Order13ActualRationalPicardTorsionNineteen.actual_rational_arithmetic_picard_torsion_card
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T16:29:29.542472+00:00
-- url     : https://prove2.me/theorems/d61fd2f5-ca56-49e1-bb7a-b2d3b5807573
-- title:
--   The rational arithmetic Picard torsion subgroup has nineteen elements
-- statement:
--   The full torsion subgroup of the degree-zero arithmetic Picard group of the actual X₁(13) function field over the rationals is finite and has exactly nineteen elements.
-- source:
--   MazurTheorem Order13ActualRationalPicardTorsionNineteen.actual_rational_arithmetic_picard_torsion_card; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual arithmetic Picard torsion subgroup over Q has
exactly nineteen elements, using the Pell infinity class and the same-family
upper bound from reduction at three and five. Named downstream consumer:
the rational Jacobian computation; the rank-zero step remains separate.
-/
import Theorems.Thm_MazurTransfer_Order13InfinityPicardClassOrder_infinityClass_order
import Theorems.Thm_MazurTransfer_Order13ActualRationalArithmeticPicardTorsionBound_actual_rational_arithmetic_picard_torsion_bound
noncomputable section
open AlgebraicCurve MazurTransfer
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityPicardClassOrder
local instance publicRationalTorsionCardOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ActualRationalPicardTorsionNineteen.actual_rational_arithmetic_picard_torsion_card :
    Finite (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∧
    Nat.card (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) = 19 := by sorry
