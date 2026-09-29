-- Prove2me | Theorems.Thm_ModularCurve_equation_tateBase_iff
-- name    : ModularCurve.equation_tateBase_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/1504518e-9d3e-5545-a5bc-946726cbc090
-- title:
--   Weierstrass equation of the Tate curve with parameter qᵖ
-- statement:
--   Let $K$ be a commutative ring, let $p$ be a natural number with $p \neq 0$, and let $x, y$ be elements of the Laurent series ring $\mathrm{LaurentSeries}\,K$. The curve in play is `tateBase K p`, obtained from the integral Weierstrass curve `tatePowerSeries` over $\mathbb{Z}[[q]]$ by first applying `laurentOfInt K`, the ring homomorphism which reduces coefficients along $\mathbb{Z} \to K$ and regards a power series as a Laurent series, and then applying `qExpand K p`, the ring endomorphism of Laurent series which multiplies all exponents by $p$, i.e. the substitution $q \mapsto q^{p}$. The assertion is that $x, y$ satisfy Mathlib's affine equation predicate for the associated affine curve `(tateBase K p).toAffine` precisely when $$y^{2} + xy = x^{3} + \mathrm{qExpand}\,K\,p\,(\mathrm{laurentOfInt}\,K\,\mathtt{tateA4})\,x + \mathrm{qExpand}\,K\,p\,(\mathrm{laurentOfInt}\,K\,\mathtt{tateA6}),$$ so that the curve's coefficients are $a_1 = 1$, $a_2 = a_3 = 0$, and $a_4$, $a_6$ the images under $q \mapsto q^{p}$ and coefficient reduction of the integral power series `tateA4`, whose $n$-th coefficient is $-\sum_{d \mid n} 5d^{3}$, and `tateA6`, whose $n$-th coefficient is $-\sum_{d \mid n} (5d^{3} + 7d^{5})/12$ (integer division by $12$, which is exact termwise); both have vanishing constant term, the divisor set of $0$ being empty.
--
--   This records the Weierstrass form of the Tate curve with parameter $q^{p}$ over $K((q))$, rewriting membership of the affine curve as an explicit identity of Laurent series with divisor-sum coefficients. It is used wherever points on this base curve must be verified, notably by [`ModularCurve.tateOrigin_equation`](thm.html#ModularCurve.tateOrigin_equation) and by the full-level statements producing modular forms whose $q$-expansion matches a cusp point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_equation_tateBase_iff.lean

import Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.equation_tateBase_iff (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (x y : LaurentSeries K) : (tateBase K p).toAffine.Equation x y ↔ y ^ 2 + x * y = x ^ 3 + qExpand K p (laurentOfInt K tateA4) * x + qExpand K p (laurentOfInt K tateA6) := by sorry
