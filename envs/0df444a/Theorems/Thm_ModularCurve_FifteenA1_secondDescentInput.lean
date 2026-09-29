-- Prove2me | Theorems.Thm_ModularCurve_FifteenA1_secondDescentInput
-- name    : ModularCurve.FifteenA1.secondDescentInput
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/145c8b37-90bc-5967-b6f9-6893600f6bd1
-- title:
--   Square certificate for halving on 15a1: kerδ=2E(ℚ)
-- statement:
--   Let `shortW` be the affine Weierstrass curve over $\mathbb{Q}$ with coefficients $(a_1,a_2,a_3,a_4,a_6)=(0,5,0,-152,-624)$, i.e. $y^2 = x^3+5x^2-152x-624 = (x-12)(x+4)(x+13)$, and let $P$ be a point of `shortW.Point`, so either the point at infinity or a nonsingular affine rational solution of that equation. The pair `deltaPair P` of rationals is $(1,1)$ at the point at infinity, and at an affine point with $x$-coordinate $X$ it is the pair whose first entry is $400$ if $X=12$ and $X-12$ otherwise, and whose second entry is $-144$ if $X=-4$ and $X+4$ otherwise. The hypotheses are that each of the two entries lies in the square class of $1$, in the sense of `IsSqClass`: there is a nonzero rational $c$ with the entry equal to $1\cdot c^2$; thus both entries are squares of nonzero rationals. The conclusion is that $P$ is divisible by $2$ in the group `shortW.Point`: there exists $Q$ with $P = 2 \bullet Q$.
--
--   This is the injectivity half of the complete $2$-descent for a curve with full rational $2$-torsion (Silverman, Proposition X.1.4), specialised to the model $y^2=(x-12)(x+4)(x+13)$ of the curve $15a1 = X_0(15)$, with the conventional replacement of the vanishing factor at each of the two-torsion points $(12,0)$ and $(-4,0)$ by the corresponding product value. It is the halving criterion used in the determination of $X_0(15)(\mathbb{Q})$, and is invoked in the proof of [`ModularCurve.FifteenA1.coords_of_equation`](thm.html#ModularCurve.FifteenA1.coords_of_equation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FifteenA1_secondDescentInput.lean

import Mathlib
import Definitions.Def_EllipticCurve_FifteenA1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.FifteenA1

theorem ModularCurve.FifteenA1.secondDescentInput (P : shortW.Point) (h1 : IsSqClass 1 (deltaPair P).1) (h2 : IsSqClass 1 (deltaPair P).2) : ∃ Q : shortW.Point, P = 2 • Q := by sorry
