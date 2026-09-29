-- Prove2me | Theorems.Thm_HopfOrder_map_eq_of_forall_le
-- name    : HopfOrder.map_eq_of_forall_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/11d08225-1804-516f-8bc3-b9e8bc4b4723
-- title:
--   The greatest Hopf order is stable under bialgebra automorphisms
-- statement:
--   Let $R$ be a commutative domain which is a principal ideal ring, $K$ a field equipped with an $R$-algebra structure making it a fraction field of $R$, and $A$ a commutative ring carrying a Hopf algebra structure over $K$ together with an $R$-algebra structure compatible with that of $K$ (scalar tower $R \to K \to A$). Let $S$ be an $R$-subalgebra of $A$ subject to five conditions: $S$ is finite as an $R$-module; the $K$-span of $S$ inside $A$ is all of $A$; for every $x \in S$ the comultiplication $\Delta(x) \in A \otimes_K A$ lies in the range of the algebra map $S \otimes_R S \to A \otimes_K A$ induced by the two inclusions $S \hookrightarrow A \to A \otimes_K A$ (`Algebra.TensorProduct.productMap` of the left and right inclusions restricted to $R$); $S$ is stable under the antipode of $A$; and $\varepsilon(S)$ is contained in the image of $R$ in $K$. Assume moreover that $S$ is maximal in the strong sense that every $R$-subalgebra $T \subseteq A$ satisfying these same five conditions is contained in $S$. Then for every $K$-bialgebra automorphism $\sigma$ of $A$, the image $\sigma(S)$, formed by restricting $\sigma$ to an $R$-algebra map, equals $S$.
--
--   This is the maximal half of Raynaud's observation that the greatest and least Hopf orders of a Hopf algebra over the fraction field are stable under the automorphisms of the generic fibre. It is used to transport an $F$-vector space structure on $A$ down to its greatest Hopf order, and is cited by [`HopfAlgebra.FVect.hopfOrder_eq_of_le`](thm.html#HopfAlgebra.FVect.hopfOrder_eq_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_map_eq_of_forall_le.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfOrder.map_eq_of_forall_le
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hmax : ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → T ≤ S)
    (σ : A ≃ₐc[K] A) :
    S.map (((σ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R) = S := by sorry
