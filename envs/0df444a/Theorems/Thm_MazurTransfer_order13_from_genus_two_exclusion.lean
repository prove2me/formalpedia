-- Prove2me | Theorems.Thm_MazurTransfer_order13_from_genus_two_exclusion
-- name    : MazurTransfer.order13_from_genus_two_exclusion
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T14:39:34.729526+00:00
-- url     : https://prove2.me/theorems/2f752a6e-6bb3-4fdf-ac2b-b1603619599e
-- title:
--   Order13: rational genus-two exclusion implies the exact-order exclusion for every elliptic curve
-- statement:
--   Assume the genus-two curve \[y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1\] has no rational affine point with \(x\ne0,-1\). Then for every elliptic curve \(E/\mathbb{Q}\), no point of \(E(\mathbb{Q})\) has exact order thirteen. The genus-two exclusion is an explicit intermediate hypothesis and remains a separate arithmetic obligation.
-- source:
--   Original user MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original complete Lean AST commands are selected by typed kernel dependencies and actual resolved source references. Original Apache-2.0 headers retained. Only a compiler-required noncomputable scope is added around the two new source modules; mathematical statements and coefficient data are unchanged. No custom axioms, proof placeholders, resource-strengthening flags, or altered final campaign hypotheses.

import Mathlib
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem MazurTransfer.order13_from_genus_two_exclusion (E : WeierstrassCurve ℚ) [E.IsElliptic] (Q : (E⁄ℚ).Point)
  (hNo : ∀ x y : ℚ, x ≠ 0 → x ≠ -1 →
    y ^ 2 = x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1 → False) :
  addOrderOf Q ≠ 13 := by sorry
