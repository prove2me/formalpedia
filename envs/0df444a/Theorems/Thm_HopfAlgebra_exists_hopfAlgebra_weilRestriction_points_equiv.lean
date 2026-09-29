-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_weilRestriction_points_equiv
-- name    : HopfAlgebra.exists_hopfAlgebra_weilRestriction_points_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/7136604b-dc04-5208-9b0d-579b43523c99
-- title:
--   Weil restriction of a cocommutative Hopf algebra along a finite free extension
-- statement:
--   Let $A$ and $B$ be commutative rings in a fixed universe with $B$ an $A$-algebra that is finite and free as an $A$-module, and let $H$ be a commutative ring carrying a Hopf algebra structure over $B$ whose comultiplication is cocommutative. The theorem asserts the existence of a type $W$ in the same universe, equipped with a commutative ring structure and a Hopf algebra structure over $A$, such that: (i) the comultiplication of $W$ over $A$ is cocommutative; and (ii) there is a family $e$ indexed by commutative $A$-algebras $T$ of bijections $e\,T \colon \mathrm{Hom}_{A\text{-alg}}(W,T) \simeq \mathrm{Hom}_{B\text{-alg}}(H, B \otimes_A T)$, taken between the two hom-sets viewed through the type synonym `WithConv` that carries the convolution product coming from the Hopf structures, with two properties. First, each $e\,T$ is multiplicative for the convolution products: $e\,T\,(f\cdot g) = e\,T\,f \cdot e\,T\,g$ for all $f,g$. Second, the family is natural in $T$: for any $A$-algebra map $u \colon T \to T'$ and any $f$, applying $e\,T'$ to the composite $u \circ f$ gives the composite of $\mathrm{id}_B \otimes u$ with $e\,T\,f$, the underlying algebra maps being passed back and forth through `WithConv.toConv` and `WithConv.ofConv`. Unit- and inverse-compatibility of $e$ are not asserted separately.
--
--   This is the existence half of the Weil restriction $\mathrm{Res}_{B/A}\operatorname{Spec} H = \operatorname{Spec} W$ for a commutative affine group scheme along a finite free extension of base rings, recorded on the Hopf-algebra side: the restricted functor of points is represented by a commutative cocommutative Hopf algebra over $A$. It is used in the construction of Weil restrictions in the étale setting, via [`HopfAlgebra.exists_weilRestriction_of_etale`](thm.html#HopfAlgebra.exists_weilRestriction_of_etale).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_weilRestriction_points_equiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem HopfAlgebra.exists_hopfAlgebra_weilRestriction_points_equiv
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [HopfAlgebra B H] [Coalgebra.IsCocomm B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : HopfAlgebra A W),
      Coalgebra.IsCocomm A W ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T],
          WithConv (W →ₐ[A] T) ≃ WithConv (H →ₐ[B] (B ⊗[A] T)),
        (∀ (T : Type u) [CommRing T] [Algebra A T] (f g : WithConv (W →ₐ[A] T)),
            e T (f * g) = e T f * e T g) ∧
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : WithConv (W →ₐ[A] T)),
          e T' (WithConv.toConv (u.comp f.ofConv))
            = WithConv.toConv ((Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f).ofConv) := by sorry
