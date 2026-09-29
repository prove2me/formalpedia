-- Prove2me | Theorems.Thm_HopfOrder_finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight
-- name    : HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/e5028cf2-70e8-593a-b4fa-ce2bcb11821c
-- title:
--   Image of an integral Hopf algebra in a generic fibre
-- statement:
--   Let $R$ be a commutative ring, $F$ a field that is an $R$-algebra, $H$ a commutative ring carrying a Hopf algebra structure over $R$ and finitely generated as an $R$-module, and $A$ a commutative ring carrying a Hopf algebra structure over $F$ together with an $R$-algebra structure compatible with $R \to F \to A$. Let $\psi \colon F \otimes_R H \to A$ be a homomorphism of $F$-bialgebras, and let $S \subseteq A$ be the $R$-subalgebra obtained as the range of the $R$-algebra map $h \mapsto \psi(1 \otimes h)$, i.e. of $\psi$ viewed over $R$ precomposed with $H \to F \otimes_R H$. Then: $S$ is finitely generated as an $R$-module; for every $x \in S$ the comultiplication $\Delta(x)$ of $A$ over $F$ lies in the range of the $R$-algebra map $S \otimes_R S \to A \otimes_F A$ given by the product of $s \mapsto s \otimes 1$ and $s \mapsto 1 \otimes s$; the antipode of $A$ over $F$ maps $S$ into $S$; and the counit of $A$ over $F$ sends every element of $S$ into the image of $R$ in $F$.
--
--   These are exactly the defining clauses of a Hopf order of $A$ over $R$ apart from the spanning condition $F \cdot S = A$, which requires $\psi$ to be surjective. The result serves as a supply lemma for constructing Hopf orders from integral models, and is used in the base-change uniqueness statement for bialgebra maps of $p$-power torsion type and in the construction of model points on a generic fibre under finiteness, flatness and inertia-stability hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open scoped TensorProduct in

theorem HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight
    {R : Type u} [CommRing R] {F : Type v} [Field F] [Algebra R F]
    {H : Type w} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {A : Type*} [CommRing A] [HopfAlgebra F A] [Algebra R A] [IsScalarTower R F A]
    (ψ : (F ⊗[R] H) →ₐc[F] A) :
    let S : Subalgebra R A :=
      (((ψ : (F ⊗[R] H) →ₐ[F] A).restrictScalars R).comp
        (Algebra.TensorProduct.includeRight : H →ₐ[R] F ⊗[R] H)).range
    Module.Finite R ↥S ∧
    (∀ x ∈ S, Coalgebra.comul (R := F) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[F] A ⊗[F] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[F] A ⊗[F] A).restrictScalars R).comp S.val)).range) ∧
    (∀ x ∈ S, HopfAlgebra.antipode F (A := A) x ∈ S) ∧
    (∀ x ∈ S, Coalgebra.counit (R := F) (A := A) x ∈ (algebraMap R F).range) := by sorry
