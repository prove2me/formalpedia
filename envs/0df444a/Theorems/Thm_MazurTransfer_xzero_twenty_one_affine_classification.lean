-- Prove2me | Theorems.Thm_MazurTransfer_xzero_twenty_one_affine_classification
-- name    : MazurTransfer.xzero_twenty_one_affine_classification
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T11:16:59.711987+00:00
-- url     : https://prove2.me/theorems/c2dbe262-2ec8-40ca-aa67-6107f4d2c5b8
-- title:
--   All rational affine points on the split X₀(21) model
-- statement:
--   The rational affine solutions of the elliptic curve $y^2=x(x-9)(x+7)$ are exactly the seven listed possibilities: $$ (x,y)\in\{(0,0),(9,0),(-7,0),(-3,12),(-3,-12),(21,84),(21,-84)\}. $$ The asserted implication is unconditional. This point classification supplies the arithmetic input for the plane-model transfer on $X_0(21)$ and the rational order-21 torsion exclusion.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion/NumberTheory/XZeroTwentyOneReduction.lean, fullTwo_affine_classification_unconditional. The original two-descent is preserved; the good-reduction cardinality interface uses the Proved theorem https://prove2.me/theorems/7f80f820-ad30-4ca2-803f-69e9cacbd186, built from generic official Anthropic FLT machinery. Original Apache-2.0 source headers retained.

import Mathlib

theorem MazurTransfer.xzero_twenty_one_affine_classification (V W : ℚ) (hcurve : W ^ 2 = V * (V - 9) * (V + 7)) :
    (V = 0 ∧ W = 0) ∨
    (V = 9 ∧ W = 0) ∨
    (V = -7 ∧ W = 0) ∨
    (V = -3 ∧ W = 12) ∨
    (V = -3 ∧ W = -12) ∨
    (V = 21 ∧ W = 84) ∨
    (V = 21 ∧ W = -84) := by sorry
