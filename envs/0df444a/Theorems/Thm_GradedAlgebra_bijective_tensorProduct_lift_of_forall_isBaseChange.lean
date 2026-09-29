-- Prove2me | Theorems.Thm_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange
-- name    : GradedAlgebra.bijective_tensorProduct_lift_of_forall_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/41017e45-b2b6-5db7-81ad-e8d294fad707
-- title:
--   Degreewise base change detects isomorphism of graded algebras
-- statement:
--   Let $S$ be a commutative ring and $T$ a commutative $S$-algebra. Let $A$ be a commutative $S$-algebra equipped with an internal $\mathbb{N}$-grading by $S$-submodules $\mathcal{A}_n \subseteq A$ (a `GradedAlgebra` structure, so $A$ is the internal direct sum of the $\mathcal{A}_n$ and the grading is multiplicative), and let $B$ be a commutative ring that is an algebra over both $T$ and $S$ compatibly (a scalar tower $S \to T \to B$), equipped with an internal $\mathbb{N}$-grading by $T$-submodules $\mathcal{B}_n \subseteq B$. Let $\vartheta : A \to B$ be an $S$-algebra homomorphism which respects the gradings in the sense that $\vartheta(x) \in \mathcal{B}_n$ for every $n$ and every $x \in \mathcal{A}_n$, and assume that for every $n$ the resulting $S$-linear map $\mathcal{A}_n \to \mathcal{B}_n$ (the target viewed as an $S$-module by restriction of scalars) exhibits $\mathcal{B}_n$ as the base change of $\mathcal{A}_n$ along $S \to T$, i.e. the induced $T$-linear map $T \otimes_S \mathcal{A}_n \to \mathcal{B}_n$ is bijective. Then the $S$-algebra homomorphism $A \otimes_S T \to B$ obtained by lifting $\vartheta$ and the structure map $T \to B$ (whose images commute, $B$ being commutative), that is $a \otimes t \mapsto t \cdot \vartheta(a)$, is bijective. No flatness or finiteness hypotheses occur.
--
--   This is the statement that an isomorphism of graded algebras after base change may be checked one graded piece at a time; it is the algebraic input behind the identification of section rings under base change, and is used in the construction of bijective algebra maps exhibiting section rings of graded structures as pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem GradedAlgebra.bijective_tensorProduct_lift_of_forall_isBaseChange
    {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
    (A : Type u) [CommRing A] [Algebra S A] (𝓐 : ℕ → Submodule S A) [GradedAlgebra 𝓐]
    (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]
    (𝓑 : ℕ → Submodule T B) [GradedAlgebra 𝓑]
    (ϑ : A →ₐ[S] B) (hϑdeg : ∀ n, ∀ x ∈ 𝓐 n, ϑ x ∈ 𝓑 n)
    (hbc : ∀ n, IsBaseChange T ((ϑ.toLinearMap.restrict (p := 𝓐 n) (q := (𝓑 n).restrictScalars S) (hϑdeg n))
      : 𝓐 n →ₗ[S] (𝓑 n).restrictScalars S)) :
    Function.Bijective
      (Algebra.TensorProduct.lift ϑ (IsScalarTower.toAlgHom S T B) (fun _ _ => Commute.all _ _) : A ⊗[S] T →ₐ[S] B) := by sorry
