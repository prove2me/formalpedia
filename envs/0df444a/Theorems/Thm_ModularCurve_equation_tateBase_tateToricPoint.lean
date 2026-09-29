-- Prove2me | Theorems.Thm_ModularCurve_equation_tateBase_tateToricPoint
-- name    : ModularCurve.equation_tateBase_tateToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/9cb01f28-5066-55ed-a0d9-92e60984b216
-- title:
--   Toric points of Tate(qᵖ) over a commutative ring
-- statement:
--   Let $K$ be a commutative ring, $p$ a natural number with $p \neq 0$, and $c \in K^{\times}$ a unit whose complement $1 - c$ is also a unit in $K$. Consider the Weierstrass curve [`ModularCurve.tateBase K p`](def/ModularCurve_TateSlots.html#L46) over the Laurent series ring $K((q))$: it is obtained from the universal Tate power-series curve by base change to $K((q))$ and then applying [`ModularCurve.qExpand K p`](def/ModularCurve_X0.html#L25), the ring homomorphism that multiplies all exponents by $p$, i.e. the substitution $q \mapsto q^{p}$. The assertion is that the pair [`ModularCurve.tateToricPoint K p c`](def/ModularCurve_KatzLevelPCusps.html#L20) satisfies the affine Weierstrass equation $y^{2} + a_1 xy + a_3 y = x^{3} + a_2 x^{2} + a_4 x + a_6$ of this curve, where the two coordinates are the power series in $q$ (viewed in $K((q))$) whose constant terms are $c \cdot (\mathrm{inv}(1-c))^{2}$ and $c^{2} \cdot (\mathrm{inv}(1-c))^{3}$ for `Ring.inverse`, and whose $m$-th coefficients for $m \geq 1$ are $\sum_{d \mid m,\ p \mid d} (m/d)\,(c^{m/d} + c^{-m/d}) \; - \; 2\,[\,p \mid m\,]\,\sigma_1(m/p)$ and $\sum_{d \mid m,\ p \mid d} \bigl(\binom{m/d}{2} c^{m/d} - \binom{m/d+1}{2} c^{-m/d}\bigr) \; + \; [\,p \mid m\,]\,\sigma_1(m/p)$ respectively, with $\sigma_1(n) = \sum_{e \mid n} e$.
--
--   This is the Tate parametrisation of the point with toric coordinate $u = c$ on the curve $\mathrm{Tate}(q^{p})$, stated over an arbitrary commutative ring in which $c$ and $1 - c$ are invertible rather than only over a field of characteristic zero. It underlies the construction of the $p$-division points supported at the cusps, and is used in [`ModularCurve.equation_tateBase_cuspPoint`](thm.html#ModularCurve.equation_tateBase_cuspPoint) and in the level-$p$ cusp statements for modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_equation_tateBase_tateToricPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.equation_tateBase_tateToricPoint
    (K : Type u) [CommRing K] (p : ℕ) [NeZero p] (c : Kˣ) (hc : IsUnit (1 - (c : K))) :
    (ModularCurve.tateBase K p).toAffine.Equation
      (ModularCurve.tateToricPoint K p c).1 (ModularCurve.tateToricPoint K p c).2 := by sorry
