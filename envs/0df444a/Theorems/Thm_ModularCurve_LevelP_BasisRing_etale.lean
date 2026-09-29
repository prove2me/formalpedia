-- Prove2me | Theorems.Thm_ModularCurve_LevelP_BasisRing_etale
-- name    : ModularCurve.LevelP.BasisRing.etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/bdbde0bc-6b7c-5443-931a-6089e6366f5c
-- title:
--   Étaleness of the level-n basis ring for nΔ invertible
-- statement:
--   Let $B$ be a commutative ring, let $W$ be a Weierstrass curve over $B$, and let $n$ be a natural number. Assume that $n$ is odd and that the element $n\cdot\Delta(W)$ of $B$, the product of the image of $n$ with the discriminant of $W$, is a unit. The ring in question is [`ModularCurve.LevelP.BasisRing W n`](def/ModularCurve_KatzLevelPUniversal.html#L163), defined as the localisation `Localization.Away (indepDenom W n)` of the two-point ring `TwoPointRing W n`, itself the torsion-point ring `TorsionPointRing` at level $n$ of the curve `torsionPtCurve W n`, i.e. the result of adjoining coordinates of a second $n$-torsion point to the ring obtained from $W$ by adjoining the coordinates of a first one; the element inverted, `indepDenom W n`, is the product of the two independence elements `indepElt` of the two-point curve formed from the $x$-coordinates `TwoPointRing.xP W n` and `TwoPointRing.xQ W n` in the two possible orders. The conclusion is `Algebra.Etale B (ModularCurve.LevelP.BasisRing W n)`: this ring is an étale $B$-algebra, that is, it is of finite presentation and formally étale over $B$.
--
--   This is the Weierstrass-coordinate incarnation of the fact that for $n$ invertible on the base the $n$-torsion of an elliptic curve is finite étale, so that the scheme parametrising bases of the $n$-torsion is étale over the base. It underlies the treatment of level-$n$ structures and their moduli data, and is used by the statements about level-$p$ structures and level moduli packages over bases where $2$, $3$ and $n$ are invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_BasisRing_etale.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.LevelP.BasisRing.etale {B : Type u} [CommRing B] (W : WeierstrassCurve B)
    {n : ℕ} (hn : Odd n) (hu : IsUnit ((n : B) * W.Δ)) :
    Algebra.Etale B (ModularCurve.LevelP.BasisRing W n) := by sorry
