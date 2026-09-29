-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_algEquiv_of_natural_mul
-- name    : HopfAlgebra.exists_hopfAlgebra_algEquiv_of_natural_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/3fd5ecd5-2405-5367-b121-3599d0716ad4
-- title:
--   Naturally group-valued functor of points yields a Hopf algebra
-- statement:
--   Let $A$ be a commutative ring and $W$ a commutative $A$-algebra, both in a fixed universe. Suppose given, for every commutative $A$-algebra $T$ in that universe, operations $\mathrm{mul}_T$ on the set of $A$-algebra maps $W \to T$, a distinguished element $\mathrm{one}_T$ of that set, and an operation $\mathrm{inv}_T$ on it, subject to: $\mathrm{mul}_T$ is associative and commutative, $\mathrm{one}_T$ is a left unit, $\mathrm{mul}_T(\mathrm{inv}_T f, f) = \mathrm{one}_T$ for all $f$, and naturality of $\mathrm{mul}$ and $\mathrm{one}$: for every $A$-algebra map $u \colon T \to T'$ one has $u \circ \mathrm{mul}_T(f,g) = \mathrm{mul}_{T'}(u \circ f, u \circ g)$ and $u \circ \mathrm{one}_T = \mathrm{one}_{T'}$. No naturality is assumed for $\mathrm{inv}$. The conclusion asserts the existence of a type $W'$ in the same universe, a commutative ring structure on it, a Hopf algebra structure over $A$ on $W'$, and an isomorphism $\psi \colon W' \cong W$ of $A$-algebras, such that the comultiplication of $W'$ is cocommutative and, for every commutative $A$-algebra $T$ and all $f, g \colon W \to T$, the map $\mathrm{mul}_T(f,g) \circ \psi$ equals the convolution product of $f \circ \psi$ and $g \circ \psi$ in the convolution monoid of maps from the coalgebra $W'$ to the algebra $T$.
--
--   This is the Yoneda-style dictionary between commutative group structures on the functor of points of an affine scheme $\operatorname{Spec} W$ over $A$ and commutative cocommutative Hopf algebra structures on $W$, in the weaker form that transports the Hopf structure along an algebra isomorphism rather than placing it on $W$ itself. It is used to equip Weil restrictions of group schemes with their Hopf algebra structure, via [`HopfAlgebra.exists_hopfAlgebra_weilRestriction_points_equiv`](thm.html#HopfAlgebra.exists_hopfAlgebra_weilRestriction_points_equiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_algEquiv_of_natural_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem HopfAlgebra.exists_hopfAlgebra_algEquiv_of_natural_mul
    (A : Type u) [CommRing A] (W : Type u) [CommRing W] [Algebra A W]
    (mul : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) → (W →ₐ[A] T) → (W →ₐ[A] T))
    (one : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T))
    (inv : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) → (W →ₐ[A] T))
    (h_assoc : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g h : W →ₐ[A] T),
      mul T (mul T f g) h = mul T f (mul T g h))
    (h_comm : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T), mul T f g = mul T g f)
    (h_one : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T (one T) f = f)
    (h_inv : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T (inv T f) f = one T)
    (h_nat_mul : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f g : W →ₐ[A] T), u.comp (mul T f g) = mul T' (u.comp f) (u.comp g))
    (h_nat_one : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T'),
      u.comp (one T) = one T') :
    ∃ (W' : Type u) (_ : CommRing W') (_ : HopfAlgebra A W') (ψ : W' ≃ₐ[A] W),
      Coalgebra.IsCocomm A W' ∧
      ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T),
        WithConv.toConv ((mul T f g).comp (ψ : W' →ₐ[A] W)) =
          WithConv.toConv (f.comp (ψ : W' →ₐ[A] W)) * WithConv.toConv (g.comp (ψ : W' →ₐ[A] W)) := by sorry
