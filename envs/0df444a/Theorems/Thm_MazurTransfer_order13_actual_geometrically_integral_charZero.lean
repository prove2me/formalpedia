-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_geometrically_integral_charZero
-- name    : MazurTransfer.order13_actual_geometrically_integral_charZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T09:31:36.660987+00:00
-- url     : https://prove2.me/theorems/c7e4d9bb-c908-4bbd-86a7-539520f13a29
-- title:
--   Geometric integrality of the actual order-13 curve over every characteristic-zero field
-- statement:
--   Let $K$ be any field of characteristic zero. Let $C/K$ be the specified curve obtained by gluing the ordinary chart
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$$
--   to its reciprocal chart by $z=x^{-1}$ and $w=yx^{-3}$. Then $C/K$ is geometrically integral: for every field extension $L/K$, the base change $C_L$ is reduced and irreducible. In particular this holds over $K=\mathbb Q$.
--
--   This establishes a geometric hypothesis required for constructing finite maps and the rational Picard representation on this actual curve.
-- source:
--   Actual curve: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Geometric-integrality criterion: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth.lean . Actual curve model and all-algebra global sections proved by Vas and contributors on Prove2Me; Apache-2.0 attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
open AlgebraicGeometry CategoryTheory

theorem MazurTransfer.order13_actual_geometrically_integral_charZero.{u} (K : Type u) [Field K] [CharZero K] :
    GeometricallyIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) := by sorry
