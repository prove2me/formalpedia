-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
-- name    : HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/90cc64c2-d0f1-5a6d-89f2-3ec174ec4c62
-- title:
--   Equivariant endomorphism of points descends to a bialgebra endomorphism
-- statement:
--   Let $D$ be a subgroup of the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $F' =$ `IntermediateField.fixedField D` be its fixed field. Let $A$ be a commutative ring carrying a Hopf algebra structure over $F'$ and finite as an $F'$-module, and write $G$ for the type $\operatorname{Hom}_{F'\text{-alg}}(A, \overline{\mathbb{Q}})$ viewed through `WithConv`, that is, equipped with its convolution monoid structure; $G$ is assumed finite. Assume that the $\overline{\mathbb{Q}}$-algebra map $\overline{\mathbb{Q}} \otimes_{F'} A \to (G \to \overline{\mathbb{Q}})$ obtained by lifting the structure map of $\overline{\mathbb{Q}}$ into the function algebra together with the $F'$-algebra map $a \mapsto (\nu \mapsto \nu(a))$ is bijective. Let $\varphi : G \to G$ be a monoid homomorphism for the convolution structure which is $D$-equivariant in the following sense: for every $\sigma \in D$ and all $\nu, \nu' \in G$, if $\nu'(a) = \sigma(\nu(a))$ for all $a \in A$, then $(\varphi \nu')(a) = \sigma((\varphi \nu)(a))$ for all $a \in A$. Then there is an $F'$-bialgebra endomorphism $u : A \to A$ with $\nu \circ u = \varphi(\nu)$ in $G$ for every $\nu \in G$.
--
--   This is the elementary direction of Galois descent for finite commutative Hopf algebras that are split by $\overline{\mathbb{Q}}$: an endomorphism of the finite point monoid compatible with the action of $D$ is induced by an endomorphism of the Hopf algebra, as a map of bialgebras. It is used in the construction of the $F'$-structure attached to such point data, in [`HopfAlgebra.exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints`](thm.html#HopfAlgebra.exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints), and relies on [`HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero`](thm.html#HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (φ : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →* WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
    (hφ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D →
      ∀ ν ν' : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
        ∀ a : A, WithConv.ofConv (φ ν') a = σ (WithConv.ofConv (φ ν) a)) :
    ∃ u : A →ₐc[↥(IntermediateField.fixedField D)] A,
      ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        WithConv.toConv ((WithConv.ofConv ν).comp (u : A →ₐ[↥(IntermediateField.fixedField D)] A)) = φ ν := by sorry
