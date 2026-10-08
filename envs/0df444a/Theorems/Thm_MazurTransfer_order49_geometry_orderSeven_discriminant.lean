-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSeven_discriminant
-- name    : MazurTransfer.order49_geometry_orderSeven_discriminant
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:06:56.314653+00:00
-- url     : https://prove2.me/theorems/3902f1bf-4ab0-4b2f-b5eb-e52e2ee0ccad
-- title:
--   Seven-isogeny geometry: orderSeven Δ
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. For every rational $d$, the Tate normal curve with parameters $b(d)$ and $c(d)$ satisfies
--   $$\Delta=d^7(d-1)^7f(d).$$
--
--   This is the original explicit discriminant identity before applying the family notation.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSeven_Δ. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
open Polynomial

theorem MazurTransfer.order49_geometry_orderSeven_discriminant (d : ℚ) :
    (MazurTorsion.Kubert.tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by sorry
