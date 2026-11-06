-- Prove2me | Theorems.Thm_LinearOptimization_ellipsoidUpdateCenter_smul
-- name    : LinearOptimization.ellipsoidUpdateCenter_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:16:25.815209+00:00
-- url     : https://prove2.me/theorems/6162ce9c-08c3-4d43-9a55-75dfcf45d10e
-- title:
--   Ellipsoid centre update is invariant under rescaling the cut
-- statement:
--   **The ellipsoid centre update is invariant under positive rescaling of the violated constraint.**
--
--   The step of Bertsimas–Tsitsiklis (p. 371) moves the centre by
--   $$c' \;=\; c+\frac{1}{n+1}\,\frac{D a}{\sqrt{a^{\mathsf T}D a}} .$$
--   Replacing $a$ by $ca$ with $c>0$ multiplies the numerator by $c$ and the square root by $c$ (since $a^{\mathsf T}Da$ scales by $c^2$), so the ratio is unchanged.
--
--   **Consequence.** A run of the ellipsoid method may use *any* positive multiple of the separating vector or subgradient it is given. This is what makes an exact rational implementation possible: the square root in the update never has to be evaluated, because it cancels — the run's centres depend only on the direction of the cut.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Theorem 8.1, p. 371, step (c); the invariance that permits exact rational arithmetic in the ellipsoid method.

import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod

open Matrix
open scoped BigOperators

namespace LinearOptimization

/-- **The centre update is invariant under positive rescaling of the cut.** -/
theorem ellipsoidUpdateCenter_smul {n : ℕ} (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    ellipsoidUpdateCenter z D (c • a) = ellipsoidUpdateCenter z D a := by sorry

end LinearOptimization
