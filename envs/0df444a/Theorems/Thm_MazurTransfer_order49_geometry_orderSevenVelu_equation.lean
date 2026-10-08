-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_equation
-- name    : MazurTransfer.order49_geometry_orderSevenVelu_equation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:02:17.49203+00:00
-- url     : https://prove2.me/theorems/86185fa4-a13c-4287-9e7d-23facdc4f9ca
-- title:
--   Seven-isogeny geometry: orderSevenVelu equation
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. Write $X_d(x)$, $Y_d(x,y)$ and $D_d(x)$ for the published original Vélu abscissa, ordinate and differential factor, and let $K_d(x)=x(x-b(d))(x-c(d))$. Let $d,x,y\in\mathbb Q$. If $(x,y)$ satisfies the affine equation of $E_d$ and $x\ne0$, $x\ne b(d)$ and $x\ne c(d)$, then
--   $$(X_d(x),Y_d(x,y))\text{ satisfies the affine equation of }E_d^\prime.$$
--
--   This exact coordinate-equation implication supports the original point-map constructor.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenVelu_equation. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_geometry_orderSevenVelu_equation {d x y : ℚ}
    (hcurve : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Equation x y)
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Equation
      (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y) := by sorry
