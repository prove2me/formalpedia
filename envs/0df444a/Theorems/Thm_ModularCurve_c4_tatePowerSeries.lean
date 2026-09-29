-- Prove2me | Theorems.Thm_ModularCurve_c4_tatePowerSeries
-- name    : ModularCurve.c4_tatePowerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/d3d7da08-0b3a-59dc-a38c-3fab22b82630
-- title:
--   The c₄ invariant of the formal Tate curve is E₄
-- statement:
--   The statement has no variables or hypotheses: it is an identity between two explicit elements of the power series ring $\mathbb{Z}[[q]]$. On the left, `tatePowerSeries` is the Weierstrass curve over $\mathbb{Z}[[q]]$ with coefficients $a_1 = 1$, $a_2 = 0$, $a_3 = 0$, $a_4 =$ `tateA4` and $a_6 =$ `tateA6`, where `tateA4` is the power series whose $n$-th coefficient is $-\sum_{d \mid n} 5 d^{3}$ and `tateA6` is the power series whose $n$-th coefficient is $-\sum_{d \mid n} \mathrm{tateB}(d)$ for the integer-valued function `tateB` (the sums being over the divisors of $n$, so both coefficients vanish at $n = 0$); `c₄` is Mathlib's invariant $c_4 = b_2^2 - 24 b_4$ of a Weierstrass curve, which for these coefficients is $1 - 48 a_4$. On the right, `eisenstein4` is the power series whose $0$-th coefficient is $1$ and whose $n$-th coefficient for $n \ge 1$ is $240 \sum_{d \mid n} d^{3}$. The theorem asserts that these two power series are equal, i.e. coefficientwise $1 - 48 a_4 = E_4$.
--
--   This is the $c_4$ half of the classical fact that the Tate curve over $\mathbb{Z}[[q]]$ has the same $c_4$ and $c_6$ invariants as the normalised weight $4$ and $6$ Eisenstein series, and hence the $j$-invariant of the Tate curve is the $q$-expansion of the modular function $j$. It is used in the computations of orders of vanishing of ratios of Eisenstein series at the places of the relevant function fields, and in identifying $c_4$-quotients with $q$-expansions of functions on $\Gamma_1$-level modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_c4_tatePowerSeries.lean

import Definitions.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open PowerSeries HahnSeries ModularCurve

theorem ModularCurve.c4_tatePowerSeries : tatePowerSeries.c₄ = eisenstein4 := by sorry
