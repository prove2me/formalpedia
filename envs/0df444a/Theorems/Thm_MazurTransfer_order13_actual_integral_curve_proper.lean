-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_integral_curve_proper
-- name    : MazurTransfer.order13_actual_integral_curve_proper
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T02:16:58.208774+00:00
-- url     : https://prove2.me/theorems/f819790a-6dcd-443f-9b17-b2f4c83875a6
-- title:
--   Actual integral order-13 curve is proper over every commutative base ring
-- statement:
--   For every commutative ring $R$, the structural morphism of the actual glued order-13 sextic curve
--
--   $$X_R\longrightarrow\operatorname{Spec} R$$
--
--   is proper. The curve $X_R$ is the literal two-chart scheme defined by $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ and its reciprocal equation, glued by $x=z^{-1}$ and $y=wz^{-3}$. There is no field, characteristic, smoothness, selected model, or properness hypothesis.
--
--   Together with the independently verified flatness, finite presentation, smoothness when $104$ is invertible, and whole-curve base-change results, this provides the actual smooth proper curve family over $\mathbb Z[1/104]$. A compatible relative Picard family, rational rank zero, and the torsion specialization argument remain separate assertions.
-- source:
--   MazurTheorem WIP, pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete selected proper projective-line, gluing, chart-preimage and finite hyperelliptic-map proofs adapted to arbitrary commutative coefficient rings at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. All attribution and per-file provenance are retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_integral_curve_proper.{u}
    (R : Type u) [CommRing R] :
    IsProper (curveToBase R) := by sorry
