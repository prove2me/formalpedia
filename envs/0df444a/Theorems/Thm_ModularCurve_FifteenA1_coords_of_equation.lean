-- Prove2me | Theorems.Thm_ModularCurve_FifteenA1_coords_of_equation
-- name    : ModularCurve.FifteenA1.coords_of_equation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/865e17df-8bcd-569e-a2a3-e88b4099a785
-- title:
--   Rational affine points of the elliptic curve 15a1
-- statement:
--   For all rational numbers $x$ and $y$ satisfying the Weierstrass equation $y^2 + xy + y = x^3 + x^2 - 10x - 10$, the pair $(x,y)$ is one of the following seven: $(-2,3)$, $(3,-2)$, $(-2,-2)$, $(-1,0)$, $(8,18)$, $(-13/4,\,9/8)$, $(8,-27)$. The assertion is a disjunction of seven conjunctions of equalities of rationals, each conjunction fixing both coordinates exactly; no integrality, nonvanishing or nonsingularity hypothesis is imposed beyond the equation itself, and the coefficients are the ones displayed, with the equation read in the field $\mathbb{Q}$. Only one direction is asserted: any rational solution of the equation appears in the list. That each of the seven listed pairs does satisfy the equation is not part of the statement, nor is any group-theoretic description of the set of solutions.
--
--   This is the determination of the affine rational points of the elliptic curve of conductor $15$ labelled 15a1, a model of the modular curve $X_0(15)$; together with the point at infinity the seven solutions make up a group of order eight. It is used by [`ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships`](thm.html#ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships) to control the rational points of the $X_0(15)$ model occurring in the treatment of $15$-isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FifteenA1_coords_of_equation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.FifteenA1.coords_of_equation (x y : ℚ) (h : y ^ 2 + x * y + y = x ^ 3 + x ^ 2 - 10 * x - 10) : (x = -2 ∧ y = 3) ∨ (x = 3 ∧ y = -2) ∨ (x = -2 ∧ y = -2) ∨ (x = -1 ∧ y = 0) ∨ (x = 8 ∧ y = 18) ∨ (x = -13 / 4 ∧ y = 9 / 8) ∨ (x = 8 ∧ y = -27) := by sorry
