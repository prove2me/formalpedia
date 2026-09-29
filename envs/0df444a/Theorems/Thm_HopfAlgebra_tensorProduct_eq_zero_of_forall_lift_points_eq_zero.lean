-- Prove2me | Theorems.Thm_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero
-- name    : HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/4f207eb2-94e1-58b0-9c22-0658f95be03a
-- title:
--   Pairs of ℚ̄-points separate A ⊗_{F'} A
-- statement:
--   Let $D$ be a subgroup of the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $F' =$ `IntermediateField.fixedField D` be its fixed field. Let $A$ be a commutative ring equipped with a Hopf algebra structure over $F'$, module-finite over $F'$, and such that the type `WithConv (A →ₐ[F'] AlgebraicClosure ℚ)` — the type synonym of the set of $F'$-algebra homomorphisms $A \to \overline{\mathbb{Q}}$, with `WithConv.ofConv` the identification back to such homomorphisms — is finite. Assume `hev`: the canonical $\overline{\mathbb{Q}}$-algebra homomorphism
--   $$\overline{\mathbb{Q}} \otimes_{F'} A \longrightarrow \bigl(\mathrm{WithConv}(\mathrm{Hom}_{F'}(A,\overline{\mathbb{Q}})) \to \overline{\mathbb{Q}}\bigr),$$
--   obtained by lifting the structure map `Algebra.ofId` of $\overline{\mathbb{Q}}$ into the function algebra together with the product of the homomorphisms `WithConv.ofConv ν`, is bijective. Then for every $x \in A \otimes_{F'} A$ such that, for all $F'$-algebra homomorphisms $\nu, \nu' : A \to \overline{\mathbb{Q}}$, the image of $x$ under the lift of the pair $(\nu,\nu')$ to $A \otimes_{F'} A \to \overline{\mathbb{Q}}$ vanishes, one has $x = 0$.
--
--   This is the statement that the $\overline{\mathbb{Q}}$-points of a finite $F'$-algebra split by $\overline{\mathbb{Q}}$ separate elements of $A \otimes_{F'} A$; it is the instance of the general separation lemma whose binders are those of the descent setting for finite commutative Hopf algebras over a fixed field of a subgroup of the absolute Galois group of $\mathbb{Q}$. It is used in [`HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints`](thm.html#HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints), where comultiplicativity of a map constructed from points is verified by testing on pairs of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero
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
    (x : A ⊗[↥(IntermediateField.fixedField D)] A)
    (hx : ∀ ν ν' : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift ν ν' (fun _ _ => Commute.all _ _) x = 0) :
    x = 0 := by sorry
