-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVeluX_eq_div
-- name    : MazurTransfer.order49_geometry_orderSevenVeluX_eq_div
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:02:05.275149+00:00
-- url     : https://prove2.me/theorems/f6dab770-b049-497b-a8f0-f66d67dfea9b
-- title:
--   Seven-isogeny geometry: orderSevenVeluX eq div
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. Write $X_d(x)$, $Y_d(x,y)$ and $D_d(x)$ for the published original Vélu abscissa, ordinate and differential factor, and let $K_d(x)=x(x-b(d))(x-c(d))$. Let $N_{X,d}(x)$ be the published original abscissa numerator. For all rational $d,x$ with $x\ne0$, $x\ne b(d)$ and $x\ne c(d)$,
--   $$X_d(x)=\frac{N_{X,d}(x)}{K_d(x)^2}.$$
--
--   This is the exact rational-function form of the original abscissa map.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenVeluX_eq_div. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_geometry_orderSevenVeluX_eq_div {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    MazurTorsion.Kubert.orderSevenVeluX d x =
      MazurTorsion.Kubert.orderSevenVeluXNumerator d x /
        MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2 := by sorry
