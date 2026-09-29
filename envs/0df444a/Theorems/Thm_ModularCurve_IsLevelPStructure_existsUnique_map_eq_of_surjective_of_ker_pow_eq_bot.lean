-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- name    : ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/9659eb2a-40f2-5f3c-bc3b-cd91dc070c0a
-- title:
--   Unique lifting of level-ℓ structures along nilpotent surjections
-- statement:
--   Let $T$ and $T'$ be commutative rings and let $\pi : T \to T'$ be a surjective ring homomorphism whose kernel is nilpotent, in the sense that $(\ker \pi)^n = \bot$ for some natural number $n$. Let $W$ be a Weierstrass curve over $T$ whose discriminant $W.\Delta$ is a unit, and let $\ell$ be a prime with $\ell \neq 2$ whose image in $T$ is a unit. Level-$\ell$ data over a ring $A$ means a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $A$, transported along a ring homomorphism componentwise; such data $D$ is a level-$\ell$ structure on a Weierstrass curve $V$ over $A$ when $(x_P,y_P)$ and $(x_Q,y_Q)$ both satisfy the affine Weierstrass equation of $V$, both $x_P$ and $x_Q$ are roots of the division polynomial $V.\mathrm{pre}\Psi\,\ell$, and the two independence elements $\prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,(V.\Psi\mathrm{Sq}\,a)(x_P) - (V.\Phi\,a)(x_P)\bigr)$ and the same expression with $x_P$ and $x_Q$ interchanged are units. Given level-$\ell$ data $D'$ over $T'$ which is a level-$\ell$ structure on the base change $W.\mathrm{map}\ \pi$, the conclusion is that there is exactly one level-$\ell$ datum $D$ over $T$ such that $D$ pushes forward along $\pi$ to $D'$ and $D$ is a level-$\ell$ structure on $W$.
--
--   This is the Hensel-type statement that the moduli problem of Katz level-$\ell$ structures is formally étale: such structures lift, uniquely, along a nilpotent thickening of the base. It is the bridge between the explicit Weierstrass-coordinate description of level structures and the deformation-theoretic arguments, and is used in the surjectivity and dual-number computations for full level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ : IsUnit ((ℓ : ℕ) : T))
    (D' : ModularCurve.LevelPData T') (hD' : ModularCurve.IsLevelPStructure (W.map π) ℓ D') :
    ∃! D : ModularCurve.LevelPData T, D.map π = D' ∧ ModularCurve.IsLevelPStructure W ℓ D := by sorry
