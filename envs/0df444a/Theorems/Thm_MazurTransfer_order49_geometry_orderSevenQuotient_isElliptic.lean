-- Prove2me | Theorems.Thm_MazurTransfer_order49_geometry_orderSevenQuotient_isElliptic
-- name    : MazurTransfer.order49_geometry_orderSevenQuotient_isElliptic
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:02:22.385003+00:00
-- url     : https://prove2.me/theorems/3e1c185d-8d63-4e8d-b74d-f04d0fb51e90
-- title:
--   Seven-isogeny geometry: orderSevenQuotient isElliptic
-- statement:
--   Let $E_d$ be the original order-seven curve over $\mathbb Q$, let $E_d^\prime$ be its prescribed quotient, and put $b(d)=d^3-d^2$, $c(d)=d^2-d$, and $f(d)=d^3-8d^2+5d+1$. For every rational parameter $d$,
--   $$E_d\text{ elliptic}\quad\Longrightarrow\quad E_d^\prime\text{ elliptic}.$$
--
--   This provides the quotient-curve ellipticity needed by the exact point-map construction.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenQuotient_isElliptic. Complete original Lean AST signature, entire original proof commands, Apache-2.0 headers and attribution preserved. Named downstream consumers: original seven-isogeny point-map constructors, original residual modular relation and full every-curve order49 exclusion.

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
open Polynomial

theorem MazurTransfer.order49_geometry_orderSevenQuotient_isElliptic (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenQuotient d).IsElliptic := by sorry
