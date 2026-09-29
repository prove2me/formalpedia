-- Prove2me | Theorems.Thm_ModularCurve_LevelP_BasisRing_faithfullyFlat
-- name    : ModularCurve.LevelP.BasisRing.faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/6052833e-5e85-5225-ad16-a65f7ed37dbf
-- title:
--   Faithful flatness of the level-p basis ring
-- statement:
--   Let $B$ be a commutative ring, $W$ a Weierstrass curve over $B$, and $p$ a prime with $p \neq 2$, and assume that the image of $p$ in $B$ is a unit and that the discriminant $W.\Delta$ is a unit. Write $\mathrm{TorsionPointRing}\,W\,p$ for the $B$-algebra attached to $W$ and $p$ by the project construction of that name, and $\mathrm{torsionPtCurve}\,W\,p$ for the Weierstrass curve obtained from $W$ over that algebra; then [`ModularCurve.LevelP.TwoPointRing W p`](def/ModularCurve_KatzLevelPUniversal.html#L112) is by definition $\mathrm{TorsionPointRing}(\mathrm{torsionPtCurve}\,W\,p)\,p$, and [`ModularCurve.LevelP.BasisRing W p`](def/ModularCurve_KatzLevelPUniversal.html#L163) is the localisation of this ring away from the element $\mathrm{indepDenom}\,W\,p$, the product of the two values of $\mathrm{indepElt}$ for the curve $\mathrm{twoPointCurve}\,W\,p$ at the two universal $x$-coordinates `TwoPointRing.xP W p` and `TwoPointRing.xQ W p`, taken in both orders. The assertion is that [`ModularCurve.LevelP.BasisRing W p`](def/ModularCurve_KatzLevelPUniversal.html#L163), with its canonical $B$-algebra structure, is faithfully flat as a $B$-module: it is flat over $B$, and $\mathfrak{m} \cdot \mathrm{BasisRing}\,W\,p \neq \mathrm{BasisRing}\,W\,p$ for every maximal ideal $\mathfrak{m}$ of $B$.
--
--   The basis ring carries the universal pair of $p$-torsion points forming a basis, so this is the statement that the scheme of bases of $W[p]$ is flat and surjective over the base (a weak form of the Katz–Mazur result that it is finite étale of degree $|GL_2(\mathbb{F}_p)|$). It is used in the construction of level-$p$ Katz modular forms, in particular by [`ModularCurve.KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant`](thm.html#ModularCurve.KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant), where descent along a faithfully flat base change is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_BasisRing_faithfullyFlat.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.BasisRing.faithfullyFlat
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpu : IsUnit (p : B)) (hW : IsUnit W.Δ) :
    Module.FaithfullyFlat B (ModularCurve.LevelP.BasisRing W p) := by sorry
