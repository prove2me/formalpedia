-- Prove2me | Theorems.Thm_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
-- name    : HopfAlgebra.exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/f20ce514-8a38-59f7-988f-60b4917fc75a
-- title:
--   Equivariant F-action on points gives an F-vector space structure
-- statement:
--   Let $D$ be a subgroup of the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and write $F' =$ `IntermediateField.fixedField D` for its fixed field. Let $A$ be a commutative ring carrying a Hopf algebra structure over $F'$ and finite as an $F'$-module, and suppose the type $\mathrm{Pt} =$ `WithConv (A →ₐ[F'] AlgebraicClosure ℚ)` of $\overline{\mathbb{Q}}$-points of $A$ — the $F'$-algebra homomorphisms $A \to \overline{\mathbb{Q}}$, equipped through `WithConv` with the convolution monoid structure, `WithConv.toConv` and `WithConv.ofConv` being the two identifications — is finite. Assume (`hev`) that the evaluation map $\overline{\mathbb{Q}} \otimes_{F'} A \to (\mathrm{Pt} \to \overline{\mathbb{Q}})$, the $\overline{\mathbb{Q}}$-algebra homomorphism obtained by lifting the structure map of $\overline{\mathbb{Q}}$ together with the product of all points, is bijective. Let $F$ be a field and let $act$ assign to each $a \in F$ a monoid endomorphism $act\,a$ of $\mathrm{Pt}$, subject to: (`hact`) for every $a \in F$, every $\sigma \in D$ and all points $\nu, \nu'$ with $\nu'(x) = \sigma(\nu(x))$ for all $x \in A$, one has $(act\,a\,\nu')(x) = \sigma((act\,a\,\nu)(x))$ for all $x \in A$; (`hadd`) $act\,(a+b)\,\nu = (act\,a\,\nu)\cdot(act\,b\,\nu)$; (`hzero`) $act\,0\,\nu = 1$; (`hmul`) $act\,(ab)\,\nu = act\,a\,(act\,b\,\nu)$; (`hone`) $act\,1\,\nu = \nu$. The conclusion is that there exists a term `fv` of [`HopfAlgebra.FVectStructure F F' A`](def/HopfAlgebra_FVectStructure.html#L11), that is, a family $a \mapsto fv.act\,a$ of $F'$-bialgebra endomorphisms of $A$ with $fv.act\,1 = \mathrm{id}$, $fv.act\,(ab) = fv.act\,a \circ fv.act\,b$, $fv.act\,0$ equal to the unit of the convolution monoid and $fv.act\,(a+b)$ equal to the convolution product of $fv.act\,a$ and $fv.act\,b$, such that for all $a \in F$ and all points $\nu$ the point $\nu \circ fv.act\,a$ equals $act\,a\,\nu$.
--
--   This is the Galois-descent step producing an $F$-vector space structure, in Raynaud's sense, on a finite commutative Hopf algebra over the fixed field of $D$ from a given $D$-equivariant $F$-action on its geometric points, under the hypothesis that the Hopf algebra is split by $\overline{\mathbb{Q}}$. It feeds the construction of normal-form models in [`HopfAlgebra.exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step`](thm.html#HopfAlgebra.exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints.lean

import Mathlib
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
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
    (F : Type*) [Field F]
    (act : F → (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →* WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)))
    (hact : ∀ a : F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D →
      ∀ ν ν' : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        (∀ x : A, WithConv.ofConv ν' x = σ (WithConv.ofConv ν x)) →
        ∀ x : A, WithConv.ofConv (act a ν') x = σ (WithConv.ofConv (act a ν) x))
    (hadd : ∀ (a b : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)), act (a + b) ν = act a ν * act b ν)
    (hzero : ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ), act 0 ν = 1)
    (hmul : ∀ (a b : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)), act (a * b) ν = act a (act b ν))
    (hone : ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ), act 1 ν = ν) :
    ∃ fv : HopfAlgebra.FVectStructure F ↥(IntermediateField.fixedField D) A,
      ∀ (a : F) (ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)),
        WithConv.toConv ((WithConv.ofConv ν).comp (fv.act a : A →ₐ[↥(IntermediateField.fixedField D)] A)) = act a ν := by sorry
