-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedSquare
-- name    : MazurTransfer.order49_geometry_orderSevenVelu_completedSquare
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:02:02.481901+00:00
-- url     : https://prove2.me/theorems/5ae0ef53-96c4-4c4d-93b8-35a32399aa4a
-- title:
--   Seven-isogeny geometry: orderSevenVelu completedSquare
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. Write $X_d(x)$, $Y_d(x,y)$ and $D_d(x)$ for the published original Vélu abscissa, ordinate and differential factor, and let $K_d(x)=x(x-b(d))(x-c(d))$. For a Weierstrass curve $W$, put $F_W(t)=4t^3+b_2(W)t^2+2b_4(W)t+b_6(W)$ and $H_W(t,u)=2u+a_1(W)t+a_3(W)$. For all rational $d,x$ with $x\ne0$, $x\ne b(d)$ and $x\ne c(d)$,
--   $$D_d(x)^2F_{E_d}(x)=F_{E_d^\prime}(X_d(x)).$$
--
--   This is the original completed-square identity for the isogeny abscissa and differential factor.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenVelu_completedSquare. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_geometry_orderSevenVelu_completedSquare {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluDifferential d x ^ 2 *
        (4 * x ^ 3 + (MazurTorsion.Kubert.orderSevenFamily d).b₂ * x ^ 2 +
          2 * (MazurTorsion.Kubert.orderSevenFamily d).b₄ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).b₆) =
      4 * MazurTorsion.Kubert.orderSevenVeluX d x ^ 3 +
        (MazurTorsion.Kubert.orderSevenQuotient d).b₂ * MazurTorsion.Kubert.orderSevenVeluX d x ^ 2 +
        2 * (MazurTorsion.Kubert.orderSevenQuotient d).b₄ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).b₆ := by sorry
