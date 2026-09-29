-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range
-- name    : HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/3f47e06f-64a7-57dd-af0f-9e8e7ed74218
-- title:
--   Galois descent: equivariant point endomorphisms come from bialgebra maps
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a $K$-algebra, and let $D$ be a subgroup of the group of $K$-algebra automorphisms of $L$ such that every $x \in L$ with $\sigma x = x$ for all $\sigma \in D$ lies in the image of $K \to L$. Let $A$ be a commutative ring which is a Hopf algebra over $K$, finite as a $K$-module, and write $G$ for the set $A \to_{K\text{-alg}} L$ of $K$-algebra maps $A \to L$, carried by the type synonym `WithConv` that equips it with the convolution monoid structure (`WithConv.ofConv` and `WithConv.toConv` being the two directions of this relabelling). Assume that the evaluation map $L \otimes_K A \to (G \to L)$, the $L$-algebra map obtained from $L \to (G \to L)$ and $a \mapsto (\nu \mapsto \nu(a))$, is bijective. Let $\varphi : G \to G$ be a homomorphism for the convolution product, and assume $\varphi$ is $D$-equivariant in the form: for $\sigma \in D$ and $\nu, \nu' \in G$ with $\nu'(a) = \sigma(\nu(a))$ for all $a \in A$, one has $\varphi(\nu')(a) = \sigma(\varphi(\nu)(a))$ for all $a \in A$. Then there is a $K$-bialgebra homomorphism $u : A \to A$ with $\nu \circ u = \varphi(\nu)$ for every $\nu \in G$.
--
--   This is the Galois-descent step for a finite commutative Hopf algebra split by $L$, over an abstract base: a $D$-equivariant convolution-monoid endomorphism of the $L$-points descends to an endomorphism of the Hopf algebra itself, bialgebra structure included. It is used in the construction of the structure produced by [`HopfAlgebra.exists_fVectStructure_of_pointAction_of_bijective_evalPoints`](thm.html#HopfAlgebra.exists_fVectStructure_of_pointAction_of_bijective_evalPoints), where an action on points is to be realised by bialgebra endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Subgroup (L ≃ₐ[K] L))
    (hfix : ∀ x : L, (∀ σ ∈ D, σ x = x) → x ∈ Set.range (algebraMap K L))
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Module.Finite K A]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L)))
    (φ : WithConv (A →ₐ[K] L) →* WithConv (A →ₐ[K] L))
    (hφ : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ ν ν' : WithConv (A →ₐ[K] L),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
        ∀ a : A, WithConv.ofConv (φ ν') a = σ (WithConv.ofConv (φ ν) a)) :
    ∃ u : A →ₐc[K] A, ∀ ν : WithConv (A →ₐ[K] L),
      WithConv.toConv ((WithConv.ofConv ν).comp (u : A →ₐ[K] A)) = φ ν := by sorry
