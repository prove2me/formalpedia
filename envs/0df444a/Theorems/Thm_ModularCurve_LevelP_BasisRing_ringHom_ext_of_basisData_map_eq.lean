-- Prove2me | Theorems.Thm_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq
-- name    : ModularCurve.LevelP.BasisRing.ringHom_ext_of_basisData_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/4eb836b6-ead3-51fd-acb9-e7350407fe94
-- title:
--   Ring maps out of the level-p basis ring are determined by basis data
-- statement:
--   Let $B$ and $A$ be commutative rings, let $W$ be a Weierstrass curve over $B$, let $p$ be a natural number, and let $\varphi : B \to A$ be a ring homomorphism. Recall that `BasisRing W p` is obtained from $B$ by the tower: first `PsiRoot W p`, the quotient of $B[X]$ by the division polynomial $W.\mathrm{pre}\Psi\,p$, then `TorsionPointRing W p`, the quotient of a polynomial ring over `PsiRoot W p` by `torsionQuadratic W p`, then the same two-step construction applied to the curve `torsionPtCurve W p` over that ring, giving `TwoPointRing W p`, and finally the localisation of `TwoPointRing W p` away from the element `indepDenom W p`; the structure map $B \to$ `BasisRing W p` is `BasisRing.ofBase W p`, and `basisData W p` is the quadruple $(x_P, y_P, x_Q, y_Q)$ of images in `BasisRing W p` of the corresponding four elements of `TwoPointRing W p`. Let $\psi, \psi' :$ `BasisRing W p` $\to A$ be ring homomorphisms whose composites with `BasisRing.ofBase W p` both equal $\varphi$, and suppose the quadruples obtained by applying $\psi$ and $\psi'$ componentwise to `basisData W p` coincide, i.e. $\psi$ and $\psi'$ agree on each of the four coordinates. Then $\psi = \psi'$.
--
--   This is the uniqueness half of the universal property of the Katz level-$p$ basis ring: a ring map out of it over the base is determined by the level structure it induces, so that the basis ring is generated over $B$ by the coordinates of the universal pair of $p$-torsion points. It is used in the construction of classifying maps for full level structures, being cited by [`ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot`](thm.html#ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot) and by the existence statements for rigid data at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq.lean

import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.LevelP

theorem ModularCurve.LevelP.BasisRing.ringHom_ext_of_basisData_map_eq
    {B : Type*} {A : Type*} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (ψ ψ' : BasisRing W p →+* A)
    (hψ : ψ.comp (BasisRing.ofBase W p) = φ) (hψ' : ψ'.comp (BasisRing.ofBase W p) = φ)
    (h : (basisData W p).map ψ = (basisData W p).map ψ') :
    ψ = ψ' := by sorry
