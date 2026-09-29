-- Prove2me | Theorems.Thm_ModularCurve_LevelP_BasisRing_flat
-- name    : ModularCurve.LevelP.BasisRing.flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/2e32bfcf-882d-5c8c-a39f-3ac67d942659
-- title:
--   The level-p basis ring is flat over the base ring
-- statement:
--   Let $B$ be a commutative ring, $W$ a Weierstrass curve over $B$, and $p$ a natural number which is odd and different from $1$ and whose image in $B$ is a unit. The ring [`ModularCurve.LevelP.BasisRing W p`](def/ModularCurve_KatzLevelPUniversal.html#L163) is, by definition, the localisation `Localization.Away (indepDenom W p)` of the two-point ring `TwoPointRing W p`, where the latter is the ring `TorsionPointRing` attached to the curve `torsionPtCurve W p` and to $p$ — that is, the $p$-torsion point ring of $W$ base-changed along its own $p$-torsion point ring — and where the element inverted, `indepDenom W p`, is the product of the two values `indepElt (twoPointCurve W p) p` taken at the pair of distinguished $x$-coordinates `TwoPointRing.xP W p`, `TwoPointRing.xQ W p` in the two possible orders. The assertion is that this ring, viewed as a module over $B$ through the structure maps, is flat: `Module.Flat B (ModularCurve.LevelP.BasisRing W p)`. No hypothesis is imposed on the discriminant of $W$, and nothing is claimed here about faithfulness of the flatness.
--
--   This is the flatness half of the basic structural property of the ring carrying the universal pair of bases of $W[p]$ in division-polynomial coordinates, in the style of the Katz–Mazur treatment of level structures. It is used in the reduction of the universal basis ring ([`ModularCurve.LevelP.isReduced_univBasisRing`](thm.html#ModularCurve.LevelP.isReduced_univBasisRing)) and in the construction of Katz-style $\Gamma_0$ forms by evaluation at the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_BasisRing_flat.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.BasisRing.flat
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) (hp : Odd p) (hp1 : p ≠ 1)
    (hpu : IsUnit (p : B)) : Module.Flat B (ModularCurve.LevelP.BasisRing W p) := by sorry
