-- Prove2me | Theorems.Thm_ModularCurve_FifteenA1_selmerBound
-- name    : ModularCurve.FifteenA1.selmerBound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/b9af8d10-1ac2-519f-a6fa-d8c0115487ba
-- title:
--   Selmer bound for the 2-descent image on 15a1
-- statement:
--   Let `shortW` be the affine Weierstrass curve over $\mathbb{Q}$ with coefficients $a_1=0$, $a_2=5$, $a_3=0$, $a_4=-152$, $a_6=-624$, that is $y^2 = x^3 + 5x^2 - 152x - 624$, and let $P$ be an arbitrary point of its group of rational points (either the point at infinity, or a pair $(X,Y)$ of rationals satisfying the equation and non-singular on the curve). Define $\mathrm{deltaPair}(P) \in \mathbb{Q}\times\mathbb{Q}$ to be $(1,1)$ at the point at infinity, and at an affine point with abscissa $X$ to be the pair whose first entry is $400$ if $X = 12$ and $X - 12$ otherwise, and whose second entry is $-144$ if $X = -4$ and $X + 4$ otherwise. The assertion is that for every such $P$ there is a pair $v$ belonging to the finite set `V₀` of pairs of rationals such that each coordinate of $\mathrm{deltaPair}(P)$ lies in the square class of the corresponding coordinate of $v$: there are non-zero rationals $c_1, c_2$ with $(\mathrm{deltaPair}\,P)_1 = v_1 c_1^2$ and $(\mathrm{deltaPair}\,P)_2 = v_2 c_2^2$.
--
--   This is the output of the complete $2$-descent on the curve $15a1 = X_0(15)$: the image of the descent map $P \mapsto (X(P)-12,\,X(P)+4)$ in $(\mathbb{Q}^\times/(\mathbb{Q}^\times)^2)^2$ is contained in the finitely many classes listed by `V₀`, which bounds $E(\mathbb{Q})/2E(\mathbb{Q})$. It is used, together with the homomorphism property [`ModularCurve.FifteenA1.deltaPairHom`](thm.html#ModularCurve.FifteenA1.deltaPairHom) of `deltaPair`, by [`ModularCurve.FifteenA1.coords_of_equation`](thm.html#ModularCurve.FifteenA1.coords_of_equation) to pin down the rational points of the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FifteenA1_selmerBound.lean

import Mathlib
import Definitions.Def_EllipticCurve_FifteenA1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.FifteenA1

theorem ModularCurve.FifteenA1.selmerBound (P : shortW.Point) : ∃ v ∈ V₀, IsSqClass v.1 (deltaPair P).1 ∧ IsSqClass v.2 (deltaPair P).2 := by sorry
