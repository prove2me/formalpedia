-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_equation
-- name    : ModularCurve.toricPoint_equation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/a6538d77-02ef-50fb-b766-05c9ade6dba4
-- title:
--   Toric points lie on the Tate curve over K((q))
-- statement:
--   Let $K$ be a field of characteristic zero, let $p$ be a nonzero natural number, and let $c \in K$ satisfy $c \neq 0$ and $c \neq 1$. Work over the Laurent series field $K((q))$ (Mathlib's `LaurentSeries K`, Hahn series with integer exponents). The curve `tateBase K p` is the Tate Weierstrass curve: the universal Tate curve over power series, with its integer coefficients mapped into $K((q))$, and then pushed forward along the ring homomorphism `qExpand K p`, which multiplies all exponents by $p$, i.e. substitutes $q^p$ for $q$. The pair `toricPoint K p c` consists of two Laurent series with no polar part, given as power series in $q$: the first has $q^0$-coefficient $c/(1-c)^2$ and, for $m \ge 1$, coefficient $\sum_{d \mid m,\ p \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\bigl[p \mid m\bigr]\sum_{e \mid m/p} e$; the second has $q^0$-coefficient $c^2/(1-c)^3$ and, for $m \ge 1$, coefficient $\sum_{d \mid m,\ p \mid d}\bigl(\binom{m/d}{2} c^{m/d} - \binom{m/d+1}{2} c^{-m/d}\bigr) + \bigl[p \mid m\bigr]\sum_{e \mid m/p} e$. The assertion is that this pair satisfies the affine Weierstrass equation of `tateBase K p`, i.e. $y^2 + xy = x^3 + a_4 x + a_6$ with $a_4, a_6$ the Tate coefficients in $q^p$.
--
--   This is the algebraic form of the Tate parametrisation at a point of the toric torus: the classical $q$-expansions $X(c,q^p)$, $Y(c,q^p)$ of the coordinates of the image of $u = c$ under $K((q))^{\times}/(q^p)^{\mathbb{Z}} \to E(K((q)))$ define a point of the Tate curve with parameter $q^p$. It is used by [`ModularCurve.equation_tateBase_tateToricPoint`](thm.html#ModularCurve.equation_tateBase_tateToricPoint) and, via the degenerate cases of the parameter, by [`ModularCurve.tateOrigin_equation`](thm.html#ModularCurve.tateOrigin_equation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_equation.lean

import Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.toricPoint_equation (K : Type*) [Field K] [CharZero K] (p : ℕ) [NeZero p] (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (tateBase K p).toAffine.Equation (toricPoint K p c).1 (toricPoint K p c).2 := by sorry
