-- Prove2me | Theorems.Thm_HopfOrder_eq_of_le_of_comap_hopfKer_eq_of_map_eq
-- name    : HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/5c7a3d1d-8bb7-5726-b471-85a6412d4d77
-- title:
--   Nested Hopf orders agreeing on a Hopf kernel and its quotient
-- statement:
--   Let $R$ be a commutative domain which is a principal ideal ring, with $K$ a field equipped with an $R$-algebra structure making it a fraction field of $R$; let $A$ and $\bar A$ be commutative rings carrying Hopf algebra structures over $K$, each also an $R$-algebra compatibly with the $R$-algebra structure on $K$, and assume the comultiplication of $A$ is cocommutative. Let $S \le S'$ be $R$-subalgebras of $A$ such that each of $S$ and $S'$ is finite as an $R$-module, spans $A$ as a $K$-submodule, has its comultiplication values on elements of the subalgebra lying in the range of the algebra map $A \otimes_K A$ induced by $a \otimes b \mapsto a \otimes 1$ and $a \otimes b \mapsto 1 \otimes b$ on the subalgebra (that is, $\Delta$ of the subalgebra lies in the image of its tensor square), is stable under the antipode of $A$, and has counit values in the image of $R \to K$. Let $\pi \colon A \to \bar A$ be a surjective homomorphism of $K$-algebras and $K$-coalgebras, and write $A_1 = \{a \in A : (\mathrm{id} \otimes \pi)\Delta(a) = a \otimes 1\}$ for its Hopf kernel, the equalizer of $(\mathrm{id} \otimes \pi)\circ\Delta$ and $a \mapsto a \otimes 1$. If the preimages of $S$ and of $S'$ in $A_1$ coincide, and the images $\pi(S)$ and $\pi(S')$ in $\bar A$ coincide, then $S = S'$.
--
--   This is the dévissage step in the uniqueness of finite flat prolongations: in scheme language, two finite flat models of one generic fibre, one contained in the other, which induce the same models of a closed subgroup scheme and of the corresponding quotient, are equal. It is used by [`HopfAlgebra.Raynaud.hopfOrder_eq_of_le_of_hasFVectDevissage`](thm.html#HopfAlgebra.Raynaud.hopfOrder_eq_of_le_of_hasFVectDevissage), where the comparison of Hopf orders is reduced along a filtration to the case of groups of type $(p,\dots,p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_eq_of_le_of_comap_hopfKer_eq_of_map_eq.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w w'
open scoped TensorProduct in

theorem HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type w'} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    {S S' : Subalgebra R A} (hle : S ≤ S')
    (hSfin : Module.Finite R ↥S)
    (hSspan : Submodule.span K (S : Set A) = ⊤)
    (hScomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hSanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hScounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hS'fin : Module.Finite R ↥S')
    (hS'span : Submodule.span K (S' : Set A) = ⊤)
    (hS'comul : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range)
    (hS'anti : ∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S')
    (hS'counit : ∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker : S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)
      = S'.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))
    (himg : S.map ((π : A →ₐ[K] Ā).restrictScalars R) = S'.map ((π : A →ₐ[K] Ā).restrictScalars R)) :
    S = S' := by sorry
