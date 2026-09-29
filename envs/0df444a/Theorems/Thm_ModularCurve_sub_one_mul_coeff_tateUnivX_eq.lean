-- Prove2me | Theorems.Thm_ModularCurve_sub_one_mul_coeff_tateUnivX_eq
-- name    : ModularCurve.sub_one_mul_coeff_tateUnivX_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/73b94c07-f4d4-5e98-abca-8b2e3b229731
-- title:
--   Coefficientwise Weierstrass ODE for the universal Tate abscissa
-- statement:
--   Let $i,k$ be natural numbers and write $[a^ib^k]$ for the coefficient functional `MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k)` on $\mathbb{Z}$-power series in two variables indexed by `Fin 2`. Two such series occur: [`ModularCurve.tateUnivX`](def/ModularCurve_TateSlots.html#L10), whose coefficient at a multi-index $e$ is $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$, is $e_0 - e_1$ when $e_1 < e_0$ and $e_0 - e_1$ divides $e_1$ (and $0$ when $e_1<e_0$ without that divisibility), and is $e_1 - e_0$ when $e_0 \le e_1$ and $e_1 - e_0$ divides $e_1$ (and $0$ otherwise); and [`ModularCurve.tateUnivA4`](def/ModularCurve_TateSlots.html#L20), supported on the diagonal, whose coefficient at $e$ with $e_0 = e_1 = n$ is the $n$-th coefficient of [`ModularCurve.tateA4`](def/ModularCurve_TateFormal.html#L29), namely $-\sum_{d \mid n} 5d^3$, and is $0$ off the diagonal. The assertion is the numerical identity $$\bigl((i-k)^2-1\bigr)\,[a^ib^k]\,X \;=\; 6\,[a^ib^k]\,X^2 \;+\; 2\,[a^ib^k]\,A_4$$ in $\mathbb{Z}$, where $X =$ [`ModularCurve.tateUnivX`](def/ModularCurve_TateSlots.html#L10) and $A_4 =$ [`ModularCurve.tateUnivA4`](def/ModularCurve_TateSlots.html#L20), the square $X^2$ being taken in the power series ring.
--
--   This is the coefficientwise form of the Weierstrass differential equation $\wp'' = 6\wp^2 - g_2/2$ for the universal Tate parametrisation, written as $D^2X = 6X^2 + X + 2A_4$ for the derivation $D$ multiplying the coefficient of $a^ib^k$ by $i-k$. It is used to express the coefficients of $(x+1/12)^2$ at the cusp, in [`ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero`](thm.html#ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero) and [`ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero`](thm.html#ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sub_one_mul_coeff_tateUnivX_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.sub_one_mul_coeff_tateUnivX_eq
    (i k : ℕ) :
    (((i : ℤ) - k) ^ 2 - 1) * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) ModularCurve.tateUnivX =
      6 * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (ModularCurve.tateUnivX ^ 2) +
        2 * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) ModularCurve.tateUnivA4 := by sorry
