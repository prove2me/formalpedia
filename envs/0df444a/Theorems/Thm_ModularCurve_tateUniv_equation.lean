-- Prove2me | Theorems.Thm_ModularCurve_tateUniv_equation
-- name    : ModularCurve.tateUniv_equation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/ca3a3813-0a41-5cca-8840-4005814fd8d3
-- title:
--   Universal Tate series satisfy the Tate Weierstrass equation
-- statement:
--   The assertion is a single closed identity in the ring $\mathbb{Z}[[T_0,T_1]]$ of formal power series in two variables, realised as `MvPowerSeries (Fin 2) ℤ`. Three elements of that ring are involved. The series `tateUnivX` has, at the exponent vector $e$, the coefficient $-2\sum_{d\mid e_1} d$ when $e_0 = e_1$, and otherwise, writing $n = |e_0 - e_1|$, the coefficient $n$ if $n \mid e_1$ and $0$ if not. The series `tateUnivY` has coefficient $\sum_{d\mid e_1} d$ when $e_0 = e_1$; when $e_1 < e_0$ it is $\binom{n}{2}$ if $n \mid e_1$ and $0$ otherwise; when $e_0 < e_1$ it is $-\binom{n+1}{2}$ if $n \mid e_1$ and $0$ otherwise (here divisor sums over $0$ are empty, so the constant term of both series vanishes). The curve `tateUnivCurve` is the Weierstrass curve with $a_1 = 1$, $a_2 = a_3 = 0$ and with $a_4$, $a_6$ the two-variable series supported on the diagonal, whose coefficient at $(m,m)$ is the degree-$m$ coefficient of the one-variable Tate series `tateA4`, resp. `tateA6`. The conclusion is that the pair $(X,Y) =$ (`tateUnivX`, `tateUnivY`) satisfies the affine Weierstrass equation of this curve, i.e. $Y^2 + XY = X^3 + a_4 X + a_6$ holds in $\mathbb{Z}[[T_0,T_1]]$.
--
--   This is the Tate parametrisation of the Tate curve written universally: the two variables play the roles of $u$ and $q/u$, so that the classical $X(u,q)$, $Y(u,q)$ expansions become a single integral power-series identity, with no convergence or inversion involved. It is the source of the on-curve assertions for points of the Tate curve used later, and is invoked in the computations of the $x$-coordinates of toric and non-toric points on `tateBase` and in the identification of Vélu quotients of the Tate curve up to variable change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateUniv_equation.lean

import Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.tateUniv_equation : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY := by sorry
