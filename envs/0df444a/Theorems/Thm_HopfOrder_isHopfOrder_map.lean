-- Prove2me | Theorems.Thm_HopfOrder_isHopfOrder_map
-- name    : HopfOrder.isHopfOrder_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/74ebbf12-1809-5a46-b6d4-4a75dcaf38f2
-- title:
--   Image of a Hopf order under a surjective Hopf quotient
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$, let $A$ and $\bar A$ be commutative Hopf algebras over $K$, each also an $R$-algebra compatibly with $K$, and let $S$ be an $R$-subalgebra of $A$ subject to the five conditions: $S$ is a finite $R$-module; the $K$-span of $S$ inside $A$ is all of $A$; for every $x \in S$ the comultiplication $\Delta(x) \in A \otimes_K A$ lies in the range of the $R$-algebra map $S \otimes_R S \to A \otimes_K A$ obtained as the product of the inclusion of $S$ into the left factor and the inclusion of $S$ into the right factor; the antipode of $A$ maps $S$ into $S$; and the counit maps $S$ into the image of $R \to K$. Let $\pi \colon A \to \bar A$ be a surjective morphism of $K$-Hopf algebras (a $K$-algebra map that is simultaneously a coalgebra map). Then the image subalgebra $\pi(S) \subseteq \bar A$, formed by pushing $S$ forward along $\pi$ viewed as an $R$-algebra map, satisfies the same five conditions: it is a finite $R$-module, its $K$-span is $\bar A$, its comultiplication lands in the range of $\pi(S) \otimes_R \pi(S) \to \bar A \otimes_K \bar A$, it is stable under the antipode of $\bar A$, and the counit sends it into the image of $R \to K$.
--
--   This is the quotient half of Raynaud's construction of models: the scheme-theoretic closure in $\operatorname{Spec} S$ of a closed subgroup of the generic fibre $\operatorname{Spec} \bar A$ is again finite flat, read on coordinate rings as the statement that a Hopf order pushes forward along a surjective Hopf algebra map. It is used in the construction and comparison of Hopf orders, for instance in the uniqueness results for finite flat models and in the production of models with prescribed points on the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_isHopfOrder_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfOrder.isHopfOrder_map
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π) :
    Module.Finite R ↥((S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    Submodule.span K (((S.map ((π : A →ₐ[K] Ā).restrictScalars R)) : Subalgebra R Ā) : Set Ā) = ⊤ ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), HopfAlgebra.antipode K (A := Ā) x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.counit (R := K) (A := Ā) x ∈ (algebraMap R K).range) := by sorry
