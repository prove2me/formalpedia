-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_equation_iff_completedSquare
-- name    : MazurTransfer.order49_geometry_equation_iff_completedSquare
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:01:40.81252+00:00
-- url     : https://prove2.me/theorems/289ae354-48ce-491d-a61f-34f0f4827c53
-- title:
--   Seven-isogeny geometry: equation iff completedSquare
-- statement:
--   Let $W$ be any Weierstrass curve over $\mathbb Q$, and let $x,y\in\mathbb Q$. Then $(x,y)$ satisfies its affine Weierstrass equation if and only if
--   $$ (2y+a_1x+a_3)^2=4x^3+b_2x^2+2b_4x+b_6. $$
--
--   This is the exact completed-square equivalence used to verify the isogeny coordinate equations.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogeny.0.MazurTorsion.Kubert.equation_iff_completedSquare. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
open Polynomial

theorem MazurTransfer.order49_geometry_equation_iff_completedSquare (W : WeierstrassCurve ℚ) (x y : ℚ) :
    W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by sorry
