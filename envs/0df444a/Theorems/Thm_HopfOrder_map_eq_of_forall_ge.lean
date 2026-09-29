-- Prove2me | Theorems.Thm_HopfOrder_map_eq_of_forall_ge
-- name    : HopfOrder.map_eq_of_forall_ge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/1e3abdff-fb87-586a-b501-a2400c7dec39
-- title:
--   Bialgebra automorphisms preserve a least Hopf order
-- statement:
--   Let $R$ be a commutative domain which is a principal ideal ring, $K$ a field which is a fraction field of $R$, and $A$ a commutative $K$-Hopf algebra which is also an $R$-algebra, the scalar actions being compatible along $R \to K \to A$. Let $S$ be an $R$-subalgebra of $A$ subject to five conditions: $S$ is finite as an $R$-module; the $K$-span of $S$ inside $A$ is all of $A$; for every $x \in S$ the comultiplication $\Delta(x) \in A \otimes_K A$ lies in the range of the $R$-algebra map $S \otimes_R S \to A \otimes_K A$ obtained as the product of the two composites of the inclusion $S \hookrightarrow A$ with `Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight`; the antipode of $A$ carries $S$ into $S$; and the counit of every element of $S$ lies in the image of $R \to K$. Assume moreover that $S$ is least with these properties: every $R$-subalgebra $T$ of $A$ satisfying the same five conditions contains $S$. Then for every isomorphism $\sigma$ of $A$ as a $K$-bialgebra (a $K$-algebra and $K$-coalgebra isomorphism $A \simeq A$), the image of $S$ under $\sigma$, viewed as an $R$-algebra map, equals $S$.
--
--   This is the minimal half of Raynaud's observation that the least Hopf order of a Hopf algebra over the fraction field is stable under all bialgebra automorphisms. It is used to transport an $F$-vector space structure to the least Hopf order, via [`HopfAlgebra.FVect.hopfOrder_eq_of_le`](thm.html#HopfAlgebra.FVect.hopfOrder_eq_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_map_eq_of_forall_ge.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfOrder.map_eq_of_forall_ge
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
    (hmin : ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → S ≤ T)
    (σ : A ≃ₐc[K] A) :
    S.map (((σ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R) = S := by sorry
