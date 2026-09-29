-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ
-- name    : ModularCurve.IsLevelPStructure.isUnit_xP_sub_xQ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/5155b13b-13fb-5fd7-9a97-2fe0f28707f8
-- title:
--   Distinct x-coordinates in a level-ℓ datum for ℓ ≥ 3
-- statement:
--   Let $T$ be a commutative ring, let $\ell$ be a prime natural number with $3 \le \ell$, and let $W$ be a Weierstrass curve over $T$. Let $D$ be a [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43) over $T$, that is, a quadruple of elements $x_P, y_P, x_Q, y_Q$ of $T$, and assume [`ModularCurve.IsLevelPStructure W ℓ D`](def/ModularCurve_KatzLevelP.html#L104), which asserts: the pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ both satisfy the affine Weierstrass equation of $W$; the polynomial $W.\mathrm{preΨ}\,\ell$ vanishes at $x_P$ and at $x_Q$; and the two elements $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units of $T$, where $$\mathrm{indepElt}\,W\,p\,x_0\,x \;=\; \prod_{a=1}^{\lfloor (p-1)/2\rfloor}\bigl(x\cdot(W.\Psi^2_a)(x_0) - (W.\Phi_a)(x_0)\bigr).$$ The conclusion is that $x_P - x_Q$ is a unit in $T$.
--
--   A basic non-degeneracy consequence of the division-polynomial formulation of a full level-$\ell$ structure: the two marked points of the datum have $x$-coordinates differing by a unit, so that expressions with $x_P - x_Q$ in the denominator make sense over any base. It is used in the construction of level-$\ell$ automorphisms and the reading of normalised witnesses on the universal datum, where such a denominator must be invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.IsLevelPStructure.isUnit_xP_sub_xQ
    {T : Type*} [CommRing T] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve T) (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    IsUnit (D.xP - D.xQ) := by sorry
