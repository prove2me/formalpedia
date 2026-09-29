-- Prove2me | Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq
-- name    : ModularCurve.LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/ff436931-7830-5f04-b7a1-2ab5bd3ce9b7
-- title:
--   Classifying map out of the torsion point ring
-- statement:
--   Let $B$ and $A$ be commutative rings, $W$ a Weierstrass curve over $B$ (given by coefficients $a_1,a_2,a_3,a_4,a_6 \in B$), $p$ a natural number, and $\varphi \colon B \to A$ a ring homomorphism. Let $x, y \in A$ be such that $(x,y)$ satisfies the affine Weierstrass equation of the base-changed curve $W.\mathrm{map}\,\varphi$, i.e. $y^2 + \varphi(a_1)xy + \varphi(a_3)y = x^3 + \varphi(a_2)x^2 + \varphi(a_4)x + \varphi(a_6)$, and such that $x$ is a root of the polynomial $\mathrm{pre}\Psi_p$ of $W.\mathrm{map}\,\varphi$. The ring $\mathtt{TorsionPointRing}\ W\ p$ is the two-step tower $\bigl(B[X]/(\mathrm{pre}\Psi_p(W))\bigr)[Y]/\bigl(Y^2 + (a_1\bar X + a_3)Y - (\bar X^3 + a_2\bar X^2 + a_4\bar X + a_6)\bigr)$, with $\mathtt{torsionPtX}$ the image of the first root $\bar X$, $\mathtt{torsionPtY}$ the second root, and $\mathtt{ofBase}$ the structural map from $B$. The assertion is that there exists a ring homomorphism $\psi$ from this ring to $A$ with $\psi \circ \mathtt{ofBase} = \varphi$, $\psi(\mathtt{torsionPtX}) = x$ and $\psi(\mathtt{torsionPtY}) = y$.
--
--   This is the existence half of the universal property of the torsion point ring: it represents, on $B$-algebras, the functor of pairs $(x,y)$ on the Weierstrass curve whose abscissa is killed by $\mathrm{pre}\Psi_p$; no hypothesis on $p$ or on the discriminant is imposed, and uniqueness is a separate matter since the two tautological coordinates generate. It is the basic tool for constructing classifying maps of level-$p$ structures, and is used in the treatment of $\Gamma_1$-points, of Katz level-$p$ forms, and in the Drinfeld-style analysis of sections of Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ModularCurve.LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq
    {B : Type u} {A : Type v} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (x y : A) (hxy : (W.map φ).toAffine.Equation x y)
    (hx : ((W.map φ).preΨ p).eval x = 0) :
    ∃ ψ : ModularCurve.LevelP.TorsionPointRing W p →+* A,
      ψ.comp (ModularCurve.LevelP.TorsionPointRing.ofBase W p) = φ ∧
        ψ (ModularCurve.LevelP.torsionPtX W p) = x ∧ ψ (ModularCurve.LevelP.torsionPtY W p) = y := by sorry
