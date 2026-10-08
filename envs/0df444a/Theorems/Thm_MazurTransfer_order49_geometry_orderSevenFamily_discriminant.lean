-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSevenFamily_discriminant
-- name    : MazurTransfer.order49_geometry_orderSevenFamily_discriminant
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:06:31.20913+00:00
-- url     : https://prove2.me/theorems/0f5f705a-2181-4f5f-a683-fd63da8a74b0
-- title:
--   Seven-isogeny geometry: orderSevenFamily Δ
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. For every $d\in\mathbb Q$,
--   $$\Delta(E_d)=d^7(d-1)^7f(d).$$
--
--   This gives the exact discriminant of the original order-seven family.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenFamily_Δ. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
open Polynomial

theorem MazurTransfer.order49_geometry_orderSevenFamily_discriminant (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenFamily d).Δ =
      d ^ 7 * (d - 1) ^ 7 *
        (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by sorry
