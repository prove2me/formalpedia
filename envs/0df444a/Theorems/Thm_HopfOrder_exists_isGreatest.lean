-- Prove2me | Theorems.Thm_HopfOrder_exists_isGreatest
-- name    : HopfOrder.exists_isGreatest
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/6903f00d-b31d-5f8b-9fc4-9ae71257a60a
-- title:
--   Existence of a greatest Hopf order
-- statement:
--   Let $R$ be a Noetherian integrally closed domain with fraction field $K$, and let $A$ be a commutative $K$-algebra carrying a Hopf algebra structure over $K$, étale over $K$, together with an $R$-algebra structure making $R \to K \to A$ a scalar tower. Suppose given an $R$-subalgebra $S \subseteq A$ such that: $S$ is finite as an $R$-module; the $K$-span of $S$ inside $A$ is all of $A$; for every $x \in S$ the comultiplication $\Delta(x) \in A \otimes_K A$ lies in the range of the algebra map $S \otimes_R S \to A \otimes_K A$ obtained as the product map of the two inclusions $S \hookrightarrow A \to A \otimes_K A$ (left and right legs, restricted to $R$-algebra maps); $S$ is stable under the antipode of $A$; and the counit sends every element of $S$ into the image of $R \to K$. Then there is an $R$-subalgebra $S_{\max} \subseteq A$ satisfying these same five conditions and such that every $R$-subalgebra $T \subseteq A$ satisfying them is contained in $S_{\max}$; that is, the set of Hopf orders of $A$, spelled out by these five clauses, has a greatest element for inclusion.
--
--   This is the existence of the maximal Hopf order (maximal prolongation) of a finite étale Hopf algebra over the fraction field of a Noetherian integrally closed domain, in the form of Raynaud's corollary on maximal orders. It is used in the comparison of Hopf orders over the base, and in the dual statement asserting the existence of a least Hopf order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_exists_isGreatest.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfOrder.exists_isGreatest
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ Smax : Subalgebra R A, (Module.Finite R ↥Smax ∧ Submodule.span K (Smax : Set A) = ⊤ ∧
        (∀ x ∈ Smax, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smax.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smax.val)).range) ∧
        (∀ x ∈ Smax, HopfAlgebra.antipode K (A := A) x ∈ Smax) ∧
        (∀ x ∈ Smax, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) ∧
      ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → T ≤ Smax := by sorry
