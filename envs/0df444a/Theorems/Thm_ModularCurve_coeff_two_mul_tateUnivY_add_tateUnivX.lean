-- Prove2me | Theorems.Thm_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX
-- name    : ModularCurve.coeff_two_mul_tateUnivY_add_tateUnivX
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/056732dd-5b52-5130-a807-f1c4ce732334
-- title:
--   2Y+X=DX for the universal Tate coordinates
-- statement:
--   Let $i,k$ be natural numbers, and let $X =$ `tateUnivX` and $Y =$ `tateUnivY` be the two fixed elements of $\mathbb{Z}[[a,b]] =$ `MvPowerSeries (Fin 2) ℤ` defined coefficientwise on an exponent $e : \mathrm{Fin}\,2 \to_{f} \mathbb{N}$ by: $X_e = -2\sum_{d \mid e_1} d$ when $e_0 = e_1$, $X_e = e_0 - e_1$ when $e_1 < e_0$ and $e_0 - e_1$ divides $e_1$, $X_e = e_1 - e_0$ when $e_0 \le e_1$, $e_0 \neq e_1$ and $e_1 - e_0$ divides $e_1$, and $X_e = 0$ in the remaining off-diagonal cases; and $Y_e = \sum_{d \mid e_1} d$ when $e_0 = e_1$, $Y_e = \binom{e_0 - e_1}{2}$ when $e_1 < e_0$ and $e_0 - e_1 \mid e_1$, $Y_e = -\binom{e_1 - e_0 + 1}{2}$ when $e_0 \le e_1$, $e_0 \neq e_1$ and $e_1 - e_0 \mid e_1$, and $Y_e = 0$ otherwise. The assertion is that the coefficient of the monomial with exponent $\mathrm{single}\,0\,i + \mathrm{single}\,1\,k$ (that is, of $a^i b^k$) in $2Y + X$ equals $(i - k)$ times the coefficient of the same monomial in $X$, the factor $i-k$ being taken in $\mathbb{Z}$.
--
--   This is the identity $2Y + X = DX$ for the universal Tate coordinate series, where $D$ is the invariant derivation multiplying the coefficient of $a^i b^k$ by $i-k$ (classically $u\,\partial/\partial u$ at fixed $Q = ab$, so that $2y+x$ is the weight-three coordinate attached to the normalised derivative of $x$). It feeds the corresponding coefficient identity at the cusp points, [`ModularCurve.coeff_two_mul_cuspPoint_snd_add_fst`](thm.html#ModularCurve.coeff_two_mul_cuspPoint_snd_add_fst).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeff_two_mul_tateUnivY_add_tateUnivX
    (i k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (2 * ModularCurve.tateUnivY + ModularCurve.tateUnivX) =
      ((i : ℤ) - k) * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) ModularCurve.tateUnivX := by sorry
