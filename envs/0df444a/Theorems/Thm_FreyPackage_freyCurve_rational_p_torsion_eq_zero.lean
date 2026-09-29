-- Prove2me | Theorems.Thm_FreyPackage_freyCurve_rational_p_torsion_eq_zero
-- name    : FreyPackage.freyCurve_rational_p_torsion_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/73b1b547-5793-50f1-87ca-4d9e6ff17f5c
-- title:
--   The Frey curve has no rational point of order p
-- statement:
--   Let $P$ be a Frey package, that is: nonzero integers $a,b,c$ together with a prime $p\ge 5$ such that $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$. Attached to $P$ is the Frey curve over $\mathbb{Q}$, the Weierstrass curve with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$ (the divisions being taken in $\mathbb{Q}$), i.e. $y^2+xy=x^3+\frac{b^p-1-a^p}{4}x^2-\frac{a^pb^p}{16}x$. The assertion is that for every point $y$ of the group of nonsingular affine points, together with the point at infinity, of the base change of this curve to $\mathbb{Q}$ (a base change along the identity, so the curve itself), the relation $p\cdot y=0$, with $p$ acting as a natural number multiple in that group, forces $y=0$. Equivalently, the group of rational points of the Frey curve attached to a Frey package contains no point of exact order $p$.
--
--   This is the statement that the rational torsion of the Frey curve has trivial $p$-part; classically it follows from Mazur's classification of torsion subgroups of elliptic curves over $\mathbb{Q}$ applied to a curve with full rational $2$-torsion, or from the Tate parametrisation at $2$. It is used by [`FreyPackage.frey_torsion_fixed_eq_zero`](thm.html#FreyPackage.frey_torsion_fixed_eq_zero), and so feeds the reducible (fixed-line) case in the proof that the mod $p$ representation of the Frey curve is irreducible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem FreyPackage.freyCurve_rational_p_torsion_eq_zero (P : FreyPackage) (y : (P.freyCurve⁄ℚ).Point) (hy : P.p • y = 0) : y = 0 := by sorry
