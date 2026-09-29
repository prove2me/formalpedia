-- Prove2me | Theorems.Thm_ModularCurve_FifteenA1_deltaPairHom
-- name    : ModularCurve.FifteenA1.deltaPairHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/86935a06-c91c-5b82-bb73-e590e2ddc9c1
-- title:
--   The 2-descent pair of 15a1 is multiplicative modulo squares
-- statement:
--   Let `shortW` be the affine Weierstrass curve over $\mathbb{Q}$ with coefficients $(a_1,a_2,a_3,a_4,a_6)=(0,5,0,-152,-624)$, that is $y^2 = x^3+5x^2-152x-624 = (x-12)(x+4)(x+13)$, and let `shortW.Point` be its Mathlib group of rational points (the point at infinity together with the nonsingular affine solutions). The map `deltaPair` sends the zero point to $(1,1)$ and an affine point with abscissa $X$ to the pair whose first entry is $400$ if $X = 12$ and $X-12$ otherwise, and whose second entry is $-144$ if $X = -4$ and $X+4$ otherwise; it depends only on the abscissa. For rational numbers $d, a$, the predicate `IsSqClass d a` asserts the existence of $c \in \mathbb{Q}$ with $c \neq 0$ and $a = d c^2$. The theorem asserts that for all points $P, Q$ of `shortW.Point` both components behave multiplicatively modulo nonzero squares: there are nonzero rationals $c_1, c_2$ with $$(\mathrm{deltaPair}(P+Q))_1 = (\mathrm{deltaPair}\,P)_1 (\mathrm{deltaPair}\,Q)_1 c_1^2, \qquad (\mathrm{deltaPair}(P+Q))_2 = (\mathrm{deltaPair}\,P)_2 (\mathrm{deltaPair}\,Q)_2 c_2^2.$$
--
--   This is the homomorphism property of the complete $2$-descent map $P \mapsto (x(P)-e_1, x(P)-e_2)$ into $(\mathbb{Q}^\times/\mathbb{Q}^{\times 2})^2$, for the curve $15a1 = X_0(15)$ in a model with all three $2$-division points rational, the values at the two $2$-torsion points with $x = 12$ and $x = -4$ being replaced by the usual products of differences of roots. It is used, together with a bound on the image of the pair map, in [`ModularCurve.FifteenA1.selmerBound`](thm.html#ModularCurve.FifteenA1.selmerBound) and in [`ModularCurve.FifteenA1.coords_of_equation`](thm.html#ModularCurve.FifteenA1.coords_of_equation), towards the determination of $E(\mathbb{Q})$ for $X_0(15)$ needed in the classification of rational cyclic $15$-isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FifteenA1_deltaPairHom.lean

import Mathlib
import Definitions.Def_EllipticCurve_FifteenA1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.FifteenA1

theorem ModularCurve.FifteenA1.deltaPairHom (P Q : shortW.Point) : IsSqClass ((deltaPair P).1 * (deltaPair Q).1) (deltaPair (P + Q)).1 ∧ IsSqClass ((deltaPair P).2 * (deltaPair Q).2) (deltaPair (P + Q)).2 := by sorry
