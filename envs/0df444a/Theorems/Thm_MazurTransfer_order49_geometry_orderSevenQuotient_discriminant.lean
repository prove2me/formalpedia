-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSevenQuotient_discriminant
-- name    : MazurTransfer.order49_geometry_orderSevenQuotient_discriminant
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:06:14.544977+00:00
-- url     : https://prove2.me/theorems/f9428521-3c66-4673-bd66-57f58e1eacdf
-- title:
--   Seven-isogeny geometry: orderSevenQuotient Δ
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. For every $d\in\mathbb Q$,
--   $$\Delta(E_d^\prime)=d(d-1)f(d)^7.$$
--
--   This is the exact discriminant formula for the prescribed quotient curve.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenQuotient_Δ. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
open Polynomial

theorem MazurTransfer.order49_geometry_orderSevenQuotient_discriminant (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
      d * (d - 1) * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ^ 7 := by sorry
