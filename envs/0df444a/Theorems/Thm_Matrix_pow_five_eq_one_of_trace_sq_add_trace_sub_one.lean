-- Prove2me | Theorems.Thm_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one
-- name    : Matrix.pow_five_eq_one_of_trace_sq_add_trace_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/0620b7f5-2de1-5fd8-8c3b-b992d7fadab5
-- title:
--   Trace criterion for g⁵=1 in SL₂(R)
-- statement:
--   Let $R$ be a commutative ring and let $g$ be a $2\times 2$ matrix over $R$ (rows and columns indexed by `Fin 2`). Assume that $\det g = 1$ and that the trace $t = \operatorname{tr} g$ satisfies the quadratic relation $t^2 + t - 1 = 0$ in $R$. The conclusion is that $g^5 = 1$ in the ring of $2\times 2$ matrices over $R$, that is, the fifth power of $g$ is the identity matrix. No nontriviality, invertibility or characteristic hypothesis on $R$ is imposed beyond commutativity, and the trace relation is required to hold exactly, not merely up to nilpotents. Note that the conclusion asserts only that the order of $g$ divides $5$; it does not assert that $g$ has order exactly $5$ (for instance over a ring in which $t^2+t-1=0$ has a solution with $g$ the corresponding scalar situation, degenerate cases are not excluded).
--
--   This is the classical trace criterion for an element of $\mathrm{SL}_2$ to satisfy $g^5 = 1$: the traces of the elements of order five are the roots $\zeta + \zeta^{-1}$, $\zeta^2 + \zeta^{-2}$ of $t^2 + t - 1$ for $\zeta$ a primitive fifth root of unity. It is used in the verification that the third division polynomial of the relevant Klein curve has nonvanishing value, [`RubinSilverberg.kleinCurve_Psi3_eval_ne_zero`](thm.html#RubinSilverberg.kleinCurve_Psi3_eval_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one.lean

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.pow_five_eq_one_of_trace_sq_add_trace_sub_one {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1) (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1 := by sorry
