-- Prove2me | Theorems.Thm_HopfOrder_isHopfOrder_comap_hopfKer
-- name    : HopfOrder.isHopfOrder_comap_hopfKer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/cfca8b0d-8bf3-50bb-b0dc-de068bbc92fa
-- title:
--   Hopf order conditions pass to the Hopf kernel
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$, let $A$ and $\bar A$ be commutative Hopf algebras over $K$ each equipped with an $R$-algebra structure compatible with that of $K$ (scalar tower), and assume the comultiplication of $A$ is cocommutative. Let $S$ be an $R$-subalgebra of $A$ subject to: $S$ is a finite $R$-module; the $K$-span of $S$ in $A$ is all of $A$; for every $x \in S$ the element $\Delta(x) \in A \otimes_K A$ lies in the range of the algebra map $S \otimes_R S \to A \otimes_K A$ induced by $s \mapsto s \otimes 1$ and $s \mapsto 1 \otimes s$; $S$ is stable under the antipode of $A$; and $\varepsilon(S)$ is contained in the image of $R$ in $K$. Let $\pi : A \to \bar A$ be a bialgebra homomorphism over $K$, and let $\mathrm{hopfKer}\,\pi$ be the $K$-subalgebra of $A$ on which the coaction $(\mathrm{id}_A \otimes \pi) \circ \Delta$ agrees with $a \mapsto a \otimes 1$, i.e. the equalizer of these two algebra maps $A \to A \otimes_K \bar A$. Then the $R$-subalgebra of $\mathrm{hopfKer}\,\pi$ obtained by pulling $S$ back along the inclusion $\mathrm{hopfKer}\,\pi \to A$ (that is, $S \cap \mathrm{hopfKer}\,\pi$) satisfies the same five conditions relative to the Hopf algebra $\mathrm{hopfKer}\,\pi$ over $K$: it is a finite $R$-module, its $K$-span is all of $\mathrm{hopfKer}\,\pi$, its comultiplications lie in the range of $(S \cap \mathrm{hopfKer}\,\pi) \otimes_R (S \cap \mathrm{hopfKer}\,\pi) \to \mathrm{hopfKer}\,\pi \otimes_K \mathrm{hopfKer}\,\pi$, it is stable under the antipode of $\mathrm{hopfKer}\,\pi$, and its counit values lie in the image of $R$.
--
--   This is the "sub-object" half of the closure operations on prolongations of finite flat group schemes: in geometric terms, for a finite flat $R$-model $\operatorname{Spec} S$ of $\operatorname{Spec} A$ and a closed subgroup $\operatorname{Spec} \bar A$, the intersection of $S$ with the Hopf kernel is a Hopf order of the quotient. It is used in the comparison of Hopf orders along dévissages, in the construction of integral models of the generic fibre, and in the multiplicativity of ranks under the Hopf-kernel/image decomposition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_isHopfOrder_comap_hopfKer.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfOrder.isHopfOrder_comap_hopfKer
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) :
    Module.Finite R ↥((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))) ∧
    Submodule.span K (((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)) : Subalgebra R ↥(HopfAlgebra.hopfKer π)) : Set ↥(HopfAlgebra.hopfKer π)) = ⊤ ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : ↥(HopfAlgebra.hopfKer π) →ₐ[K] ↥(HopfAlgebra.hopfKer π) ⊗[K] ↥(HopfAlgebra.hopfKer π)).restrictScalars R).comp ((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : ↥(HopfAlgebra.hopfKer π) →ₐ[K] ↥(HopfAlgebra.hopfKer π) ⊗[K] ↥(HopfAlgebra.hopfKer π)).restrictScalars R).comp ((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), HopfAlgebra.antipode K (A := ↥(HopfAlgebra.hopfKer π)) x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))) ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), Coalgebra.counit (R := K) (A := ↥(HopfAlgebra.hopfKer π)) x ∈ (algebraMap R K).range) := by sorry
