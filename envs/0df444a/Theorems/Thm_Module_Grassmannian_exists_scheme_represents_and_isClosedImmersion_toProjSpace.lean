-- Prove2me | Theorems.Thm_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace
-- name    : Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/fb2845df-c4b7-5abd-953d-188f38e92fb7
-- title:
--   Representability and projectivity of the Grassmannian of a finite module
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module that is finite as an $R$-module, and $k$ a natural number. The assertion is the existence of: a scheme $\mathrm{Gr}$ (in the bottom universe), a morphism $p : \mathrm{Gr} \to \operatorname{Spec} R$, and a family of bijections $pt$, one for each commutative ring $A$ equipped with an $R$-algebra structure, between the Grassmannian `Module.Grassmannian A (A ⊗[R] M) k` — the $A$-submodules of $A \otimes_R M$ with projective quotient of rank $k$ — and the set of those morphisms $g : \operatorname{Spec} A \to \mathrm{Gr}$ satisfying $p \circ g = \operatorname{Spec}(\text{algebraMap } R\,A)$, i.e. morphisms over $\operatorname{Spec} R$; such that two further conditions hold. First, naturality: for $R$-algebras $A$, $B$, an $R$-algebra homomorphism $\varphi : A \to B$ and $N$ in the Grassmannian over $A$, the morphism attached by $pt$ over $B$ to the base change `Module.Grassmannian.map φ N` is $\operatorname{Spec}\varphi$ followed by the morphism attached to $N$ over $A$. Second, projectivity: there are a natural number $m$ and a morphism $\iota$ from $\mathrm{Gr}$ to $\operatorname{Proj}$ of the graded ring $\bigoplus_d$ `MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R` $d$ such that $\iota$ is a closed immersion and $\iota$ followed by the morphism `ProjSpace.π R m` to $\operatorname{Spec} R$ equals $p$. Only affine test objects occur: the bijections are asserted for $R$-algebras $A$ that are types in the bottom universe.
--
--   This is Grothendieck's representability of the Grassmannian functor of rank-$k$ locally free quotients of a finite module, together with the projectivity of the representing scheme over the base. It is used for the corresponding statement with the Hopf-ideal refinement and, through the Hilbert functor of subschemes of bounded growth, in the construction of the moduli spaces needed downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ) :
    ∃ (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        Module.Grassmannian A (A ⊗[R] M) k ≃
          {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : Module.Grassmannian A (A ⊗[R] M) k),
        (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1) ∧
      ∃ (m : ℕ) (ι : Gr ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)),
        IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R m = p := by sorry
