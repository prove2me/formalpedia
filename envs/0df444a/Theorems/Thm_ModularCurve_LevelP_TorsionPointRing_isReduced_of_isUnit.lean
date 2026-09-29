-- Prove2me | Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_isReduced_of_isUnit
-- name    : ModularCurve.LevelP.TorsionPointRing.isReduced_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/680595ea-ffe0-55d8-a8a9-c9ec91693930
-- title:
--   Reducedness of the universal p-torsion point ring
-- statement:
--   Let $B$ be a commutative ring which is a domain, let $W$ be a Weierstrass curve over $B$ with discriminant $W.\Delta$ and coefficients $a_1,a_2,a_3,a_4,a_6$, and let $p$ be a natural number which is odd and different from $1$ (so $p\ge 3$; no primality is assumed). Assume that $(p : B)\cdot W.\Delta$ is a unit of $B$. Consider first $\mathrm{PsiRoot}\,W\,p =$ `AdjoinRoot (W.preΨ p)`, obtained from $B$ by adjoining a root $x$ of the $p$-division polynomial `W.preΨ p`, the root itself being denoted `psiRootX W p`; over this ring form the monic quadratic
--   $$\mathrm{torsionQuadratic} = Y^2 + (a_1x + a_3)\,Y - (x^3 + a_2x^2 + a_4x + a_6),$$
--   and let $\mathrm{TorsionPointRing}\,W\,p$ be `AdjoinRoot` of this quadratic, i.e. the result of adjoining a root $y$ of the Weierstrass equation at the abscissa $x$. The assertion is that this ring, $B[x,y]/(\psi_p(x),\,W(x,y))$, is reduced: it has no nonzero nilpotent elements.
--
--   This is the reducedness half of the standard fact that, away from $p$ and from the discriminant, the universal ring carrying a point of order $p$ on a Weierstrass curve is an étale $B$-algebra, in the form used for level-$p$ structures in the sense of Katz–Mazur. It is used in the Drinfeld-level part of the development, for the identification of sections of order dividing $n$ with zeros of division polynomials and for the associated unit statement about line polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_TorsionPointRing_isReduced_of_isUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.LevelP.TorsionPointRing.isReduced_of_isUnit
    {B : Type} [CommRing B] [IsDomain B] (W : WeierstrassCurve B) {p : ℕ}
    (hp : Odd p) (hp1 : p ≠ 1) (hu : IsUnit ((p : B) * W.Δ)) :
    IsReduced (ModularCurve.LevelP.TorsionPointRing W p) := by sorry
