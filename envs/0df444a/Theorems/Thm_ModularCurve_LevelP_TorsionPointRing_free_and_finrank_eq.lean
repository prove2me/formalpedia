-- Prove2me | Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq
-- name    : ModularCurve.LevelP.TorsionPointRing.free_and_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/35be7bb4-ebe8-56ca-badb-e9be5885a28f
-- title:
--   Freeness and rank p²-1 of the p-torsion point ring
-- statement:
--   Let $B$ be a nontrivial commutative ring and let $W$ be a Weierstrass curve over $B$, with coefficients $a_1,a_2,a_3,a_4,a_6$. Let $p$ be a natural number which is odd, different from $1$, and whose image in $B$ is a unit. Consider first the ring $\mathrm{PsiRoot}\,W\,p = B[X]/(\mathrm{preΨ}_p)$ obtained by adjoining a root of Mathlib's pre-division polynomial $\mathrm{preΨ}_p \in B[X]$ of $W$, and write $x$ for the class of $X$ in it; then [`ModularCurve.LevelP.TorsionPointRing W p`](def/ModularCurve_KatzLevelPUniversal.html#L51) is the ring obtained from $\mathrm{PsiRoot}\,W\,p$ by adjoining a root of the quadratic
--   $$Y^2 + (a_1x + a_3)\,Y - (x^3 + a_2x^2 + a_4x + a_6),$$
--   i.e. the affine coordinate ring of the locus of points of $W$ whose abscissa is annihilated by the $p$-division polynomial, viewed as a $B$-algebra through the tower $B \to \mathrm{PsiRoot}\,W\,p \to \mathrm{TorsionPointRing}\,W\,p$. The assertion is the conjunction of two statements: this ring is a free $B$-module, and its $B$-rank (`Module.finrank`) equals $p^2 - 1$.
--
--   This is the standard computation that the scheme of points of exact order $p$ on a Weierstrass curve is of degree $p^2-1$ over the base, here in the form of freeness of the coordinate ring together with its rank: the pre-division polynomial has degree $(p^2-1)/2$ and leading coefficient $p$, which is invertible, and the Weierstrass equation is a monic quadratic in the ordinate. It underlies the flatness and faithful flatness of the universal level-$p$ basis ring and the uniqueness statement for pullbacks of level-$p$ structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.TorsionPointRing.free_and_finrank_eq
    {B : Type u} [CommRing B] [Nontrivial B] (W : WeierstrassCurve B) {p : ℕ} (hp : Odd p)
    (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Module.Free B (ModularCurve.LevelP.TorsionPointRing W p) ∧
      Module.finrank B (ModularCurve.LevelP.TorsionPointRing W p) = p ^ 2 - 1 := by sorry
