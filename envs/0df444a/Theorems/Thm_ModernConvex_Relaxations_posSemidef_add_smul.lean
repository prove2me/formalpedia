-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_posSemidef_add_smul
-- name    : ModernConvex.Relaxations.posSemidef_add_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:10.428863+00:00
-- url     : https://prove2.me/theorems/0c63616c-b69b-439b-84a5-b1766434b3a1
-- title:
--   The positive semidefinite cone is convex
-- statement:
--   **The cone of positive semidefinite matrices is convex.**
--
--   If $X,Y\succeq0$ and $a,b\ge0$ then $aX+bY\succeq0$: it is symmetric, and for every $v$
--   $$v^{\mathsf T}(aX+bY)v=a\,v^{\mathsf T}Xv+b\,v^{\mathsf T}Yv\ge0 .$$
--   Equivalently, in the partial order on symmetric matrices, the nonnegative elements form a convex cone, so $aX+bY\ge0$ whenever $X,Y\ge0$ and $a,b\ge0$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, p. 170; convexity of the MAXCUT SDP feasible set.

import Mathlib

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The positive semidefinite cone is convex**: nonnegative linear combinations of positive
semidefinite matrices are positive semidefinite. -/
theorem posSemidef_add_smul {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • X + b • Y).PosSemidef := by sorry

end ModernConvex.Relaxations
