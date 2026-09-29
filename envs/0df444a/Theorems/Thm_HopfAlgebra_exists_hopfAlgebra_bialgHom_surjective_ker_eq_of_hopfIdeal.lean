-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
-- name    : HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/260110ef-5ff2-5add-a5bd-ea46d6cb2677
-- title:
--   Hopf ideals admit Hopf quotients over a field
-- statement:
--   Let $F$ be a field and $A$ a commutative ring carrying the structure of a Hopf $F$-algebra, and let $I \subseteq A$ be an ideal satisfying the three conditions that make it a Hopf ideal: for every $a \in I$ the image of $\mathrm{comul}(a) \in A \otimes_F A$ under the map $A \otimes_F A \to (A/I) \otimes_F (A/I)$ induced by the quotient algebra map $A \to A/I$ in both factors vanishes; the counit kills $I$; and the antipode maps $I$ into $I$. The assertion is the existence of a type $A'$ in the same universe as $A$, equipped with a commutative ring structure and a Hopf $F$-algebra structure, together with an $F$-bialgebra homomorphism $\pi \colon A \to A'$ such that: $\pi$ is surjective; the kernel of $\pi$ as a ring homomorphism equals $I$; $A'$ is cocommutative whenever $A$ is; $A'$ is finite-dimensional over $F$ whenever $A$ is; and $\pi$ has the universal property of the quotient in commutative $F$-algebras, namely for every commutative $F$-algebra $T$ and every $F$-algebra map $\varphi \colon A \to T$ with $I$ contained in the kernel of $\varphi$ there is a unique $F$-algebra map $\varphi' \colon A' \to T$ with $\varphi' \circ \pi = \varphi$.
--
--   This is the standard construction of the quotient Hopf algebra $A/I$ attached to a Hopf ideal $I$, equivalently of the closed subgroup scheme $\operatorname{Spec}(A/I) \subseteq \operatorname{Spec}(A)$, packaged existentially as a type with its instances and the projection rather than as instances on $A/I$ itself, with the conclusions needed downstream (surjectivity, prescribed kernel, inheritance of cocommutativity and of finiteness over $F$, and the factorisation property) bundled into the statement. It is used in the construction of Hopf-algebra models, notably for the vanishing ideal of a submonoid of points and in the passage to a model with prescribed generic fibre for finite flat group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
open scoped TensorProduct

theorem HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
    {F : Type u} [Field F] {A : Type v} [CommRing A] [HopfAlgebra F A] (I : Ideal A)
    (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)
      (Coalgebra.comul (R := F) a) = 0)
    (hcounit : ∀ a ∈ I, Coalgebra.counit (R := F) a = 0)
    (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := F) a ∈ I) :
    ∃ (A' : Type v) (_ : CommRing A') (_ : HopfAlgebra F A') (π : A →ₐc[F] A'),
      Function.Surjective π ∧
      RingHom.ker (π : A →+* A') = I ∧
      (Coalgebra.IsCocomm F A → Coalgebra.IsCocomm F A') ∧
      (Module.Finite F A → Module.Finite F A') ∧
      (∀ (T : Type v) [CommRing T] [Algebra F T] (φ : A →ₐ[F] T),
        I ≤ RingHom.ker (φ : A →+* T) → ∃! φ' : A' →ₐ[F] T, φ'.comp (π : A →ₐ[F] A') = φ) := by sorry
