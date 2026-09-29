-- Prove2me | Theorems.Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq
-- name    : ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/3e366cac-0970-57e5-b45d-4f690b18bb89
-- title:
--   Existence of the classifying map of a level-p structure
-- statement:
--   Let $B$ and $A$ be commutative rings, $W$ a Weierstrass curve over $B$, $p$ a natural number, $\varphi : B \to A$ a ring homomorphism, and $D = (x_P, y_P, x_Q, y_Q)$ a quadruple of elements of $A$ (a [`ModularCurve.LevelPData A`](def/ModularCurve_KatzLevelP.html#L43)). Assume [`ModularCurve.IsLevelPStructure (W.map φ) p D`](def/ModularCurve_KatzLevelP.html#L104), i.e. for the base-changed curve $W^{\varphi} = W.\mathrm{map}\,\varphi$ over $A$: the pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ both satisfy the affine Weierstrass equation of $W^{\varphi}$, the polynomial $(W^{\varphi}).\mathrm{pre}\Psi\,p$ vanishes at $x_P$ and at $x_Q$, and both independence elements $\prod_{a=1}^{(p-1)/2}\bigl(x_Q\,(W^{\varphi}.\Psi\mathrm{Sq}\,a)(x_P) - (W^{\varphi}.\Phi\,a)(x_P)\bigr)$ and the same expression with $x_P$ and $x_Q$ exchanged are units in $A$. The conclusion is that there exists a ring homomorphism $\psi$ from [`ModularCurve.LevelP.BasisRing W p`](def/ModularCurve_KatzLevelPUniversal.html#L163) — the ring obtained from $B$ by adjoining a root of $W.\mathrm{pre}\Psi\,p$, then a root of the associated Weierstrass quadratic, repeating this pair of steps for a second point, and finally localising away from `indepDenom W p` — to $A$ such that $\psi$ composed after [`ModularCurve.LevelP.BasisRing.ofBase W p`](def/ModularCurve_KatzLevelPUniversal.html#L176) equals $\varphi$, and such that applying $\psi$ coordinatewise to the tautological quadruple [`ModularCurve.LevelP.basisData W p`](def/ModularCurve_KatzLevelPUniversal.html#L202) gives $D$. No hypothesis is imposed on $p$ or on the discriminant of $W$.
--
--   This is the existence half of the statement that $\operatorname{Spec}$ of the basis ring represents pairs of $p$-torsion points in division-polynomial coordinates satisfying the independence conditions: every level-$p$ structure on a base change of $W$ arises from a unique classifying map. It feeds the uniqueness refinement [`ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot`](thm.html#ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot) and the full-level moduli constructions built on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq
    {B : Type u} {A : Type v} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (D : ModularCurve.LevelPData A)
    (hD : ModularCurve.IsLevelPStructure (W.map φ) p D) :
    ∃ ψ : ModularCurve.LevelP.BasisRing W p →+* A,
      ψ.comp (ModularCurve.LevelP.BasisRing.ofBase W p) = φ ∧
        (ModularCurve.LevelP.basisData W p).map ψ = D := by sorry
