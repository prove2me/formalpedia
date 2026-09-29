-- Prove2me | Theorems.Thm_FreyPackage_freyCurve_discriminant
-- name    : FreyPackage.freyCurve_discriminant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/63f716b9-85dd-5be7-a9f5-539fb8996c1a
-- title:
--   Discriminant of the Frey curve: (abc)²ᵖ/2⁸
-- statement:
--   Let $P$ be a Frey package, i.e. a tuple consisting of nonzero integers $a$, $b$, $c$, a prime $p$ with $p \ge 5$, a solution of the Fermat equation $a^p + b^p = c^p$, and the normalisations $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$. Associated to $P$ is the Weierstrass curve [`FreyPackage.freyCurve`](def/FLTPrelim_FreyPackage.html#L90) over $\mathbb{Q}$ with coefficients $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$, that is the model $y^2 + xy = x^3 + \tfrac{b^p - 1 - a^p}{4} x^2 - \tfrac{a^p b^p}{16} x$. The assertion is the identity in $\mathbb{Q}$
--   $$\Delta = \frac{(abc)^{2p}}{2^8},$$
--   where $\Delta$ is the Mathlib discriminant $-b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6$ of this Weierstrass model. The statement is an equality of rational numbers only; no non-vanishing, integrality or minimality claim is made.
--
--   This is the classical discriminant computation for the Frey–Hellegouarch curve attached to a putative Fermat solution, in the form $\Delta = 2^{-8}(ABC)^2$ with $A = a^p$, $B = b^p$, $C = c^p$. It underlies the reduction-type and level computations for the Frey curve, and is cited in the project by the results on $p$-torsion points with integral abscissa and on the inertia filtration at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_freyCurve_discriminant.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem FreyPackage.freyCurve_discriminant (P : FreyPackage) : P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by sorry
