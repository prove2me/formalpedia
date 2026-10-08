-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_completedY
-- name    : MazurTransfer.order49_geometry_orderSevenVelu_completedY
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:02:08.053992+00:00
-- url     : https://prove2.me/theorems/10a81bed-6060-460c-a7a8-9d1420fd031b
-- title:
--   Seven-isogeny geometry: orderSevenVelu completedY
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. Write $X_d(x)$, $Y_d(x,y)$ and $D_d(x)$ for the published original Vélu abscissa, ordinate and differential factor, and let $K_d(x)=x(x-b(d))(x-c(d))$. For a Weierstrass curve $W$, put $F_W(t)=4t^3+b_2(W)t^2+2b_4(W)t+b_6(W)$ and $H_W(t,u)=2u+a_1(W)t+a_3(W)$. For all rational $d,x,y$,
--   $$H_{E_d^\prime}(X_d(x),Y_d(x,y))=D_d(x)H_{E_d}(x,y).$$
--
--   This is the exact original completed-ordinate identity, with no additional hypothesis on the abscissa.
--
--   **Formalization Note:** These are the published total coordinate formulas. Rational division is totalized, so this identity also covers their specified values at kernel abscissas.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenVelu_completedY. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_geometry_orderSevenVelu_completedY (d x y : ℚ) :
    2 * MazurTorsion.Kubert.orderSevenVeluY d x y +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₁ * MazurTorsion.Kubert.orderSevenVeluX d x +
        (MazurTorsion.Kubert.orderSevenQuotient d).a₃ =
      MazurTorsion.Kubert.orderSevenVeluDifferential d x *
        (2 * y + (MazurTorsion.Kubert.orderSevenFamily d).a₁ * x +
          (MazurTorsion.Kubert.orderSevenFamily d).a₃) := by sorry
