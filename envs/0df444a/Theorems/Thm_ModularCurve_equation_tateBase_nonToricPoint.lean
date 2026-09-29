-- Prove2me | Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
-- name    : ModularCurve.equation_tateBase_nonToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/8181f8ab-346b-52f1-82c6-c1396da6f125
-- title:
--   The non-toric slot point lies on the base Tate curve
-- statement:
--   Let $K$ be a commutative ring, let $p$ be a natural number that is nonzero, let $c$ be a unit of $K$, and let $j$ be a natural number with $0 < j$ and $j < p$. Consider the Weierstrass curve `tateBase K p` over the Laurent series field $K((q))$: it is obtained from the universal Tate Weierstrass curve over $\mathbb{Z}[[q]]$ by base change along $\mathbb{Z}[[q]] \to K((q))$, followed by the ring homomorphism `qExpand K p`, which rescales all Hahn-series exponents by the factor $p$ (so that the resulting curve is the Tate curve in the parameter $q^p$). Consider further the pair `nonToricPoint K p c j` of Laurent series over $K$, whose two coordinates are the images in $K((q))$ of the power series obtained by substituting the family `slotFamily K p c j` into the two universal two-variable power series `tateUnivX` and `tateUnivY` over $\mathbb{Z}$, whose coefficients at a multi-exponent $(e_0,e_1)$ are, respectively, $-2\sum_{d \mid e_1} d$ and $\sum_{d \mid e_1} d$ on the diagonal $e_0 = e_1$, and off the diagonal are $|e_0-e_1|$, resp. $\pm\binom{|e_0-e_1|}{2}$-type binomial values, whenever $|e_0 - e_1|$ divides $e_1$ and $0$ otherwise. The assertion is that this pair satisfies the affine Weierstrass equation of `tateBase K p`, that is, $y^2 + a_1xy + a_3y - x^3 - a_2x^2 - a_4x - a_6 = 0$ for the coefficients of that curve.
--
--   This is the on-curve identity for the points of the Tate parametrisation attached to a parameter $u = c\,q^{j}$ with $0 < j < p$, i.e. a point of the Tate curve $E_{q^p}$ over $K((q))$ not lying in the toric part; the statement holds over an arbitrary commutative coefficient ring, the corresponding assertion over fields of characteristic zero being [`ModularCurve.nonToricPoint_equation`](thm.html#ModularCurve.nonToricPoint_equation). It supplies the points used in the construction of the degeneracy and quotient maps at level $p$ and in the computations with $q$-expansions at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_equation_tateBase_nonToricPoint.lean

import Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.equation_tateBase_nonToricPoint (K : Type*) [CommRing K] (p : ℕ)
    [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (tateBase K p).toAffine.Equation (nonToricPoint K p c j).1 (nonToricPoint K p c j).2 := by sorry
