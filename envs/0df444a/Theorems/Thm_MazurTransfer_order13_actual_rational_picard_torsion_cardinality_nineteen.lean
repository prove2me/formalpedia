-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_rational_picard_torsion_cardinality_nineteen
-- name    : MazurTransfer.order13_actual_rational_picard_torsion_cardinality_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T17:53:44.49752+00:00
-- url     : https://prove2.me/theorems/636f5859-7b20-4653-a661-51ddd038c9fe
-- title:
--   Rational Picard torsion cardinality for the arithmetic norm maps
-- statement:
--   The full torsion subgroup of the degree-zero arithmetic Picard group of the actual X₁(13) function field over the rationals is finite and has nineteen elements. This is the existing accepted cardinality statement, exposed with the original arithmetic group constructors and minimal statement dependencies for the norm-kernel computation.
-- source:
--   Compatibility interface for the accepted MazurTheorem Order13ActualRationalPicardTorsionNineteen.actual_rational_arithmetic_picard_torsion_card; original full type retained; official Anthropic FLT arithmetic Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
noncomputable section
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance publicMinimalRationalPicardTorsionFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.order13_actual_rational_picard_torsion_cardinality_nineteen :
    Finite (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∧
    Nat.card (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) = 19 := by sorry
