-- Prove2me | Theorems.Thm_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange
-- name    : HopfOrder.isHopfOrder_range_includeRight_comp_of_surjective_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/9966400a-09a4-5fda-b5f2-eb45eebb7b94
-- title:
--   A generically surjective bialgebra map yields a Hopf order
-- statement:
--   Let $R$ be a commutative ring, $F$ a field equipped with an $R$-algebra structure, $H$ a commutative $R$-algebra carrying a Hopf algebra structure over $R$ and finite as an $R$-module, and $H'$ a commutative $R$-algebra carrying a Hopf algebra structure over $R$. Let $\varphi \colon H \to H'$ be a morphism of $R$-bialgebras and assume that the base change along $R \to F$ of the underlying $R$-linear map of $\varphi$ is surjective as a map $F \otimes_R H \to F \otimes_R H'$. Write $S$ for the $R$-subalgebra of $F \otimes_R H'$ that is the range of $\varphi$ followed by the inclusion `Algebra.TensorProduct.includeRight` of $H'$ into $F \otimes_R H'$. The assertion is the conjunction of six statements: $S$ is finite as an $R$-module; the $F$-submodule of $F \otimes_R H'$ spanned by $S$ is all of $F \otimes_R H'$; for every $x \in S$ the comultiplication of $x$ in the $F$-coalgebra $F \otimes_R H'$ lies in the range of the algebra map $S \otimes_R S \to (F \otimes_R H') \otimes_F (F \otimes_R H')$ obtained as the product map of the two composites of the inclusion $S \hookrightarrow F \otimes_R H'$ with the left and the right inclusion into the $F$-tensor square, scalars restricted to $R$; the antipode of the $F$-Hopf algebra $F \otimes_R H'$ carries $S$ into $S$; the $F$-counit of every $x \in S$ lies in the image of $R$ in $F$; and $S$ is contained in the range of `Algebra.TensorProduct.includeRight` on $H'$.
--
--   This realises the image of $H$ in the generic fibre $F \otimes_R H'$ as a Hopf order of that fibre which is moreover contained in the image of $H'$, the configuration to which lattice comparison arguments for prolongations of finite flat group schemes are applied. It is used in the proofs that base change of suitable Hopf algebras along $R \to F$ is bijective and in the uniqueness statement for bialgebra maps determined after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfOrder.isHopfOrder_range_includeRight_comp_of_surjective_baseChange
    {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type*} [CommRing H'] [HopfAlgebra R H']
    (φ : H →ₐc[R] H')
    (hφ : Function.Surjective ((φ : H →ₐ[R] H').toLinearMap.baseChange F)) :
    let S : Subalgebra R (F ⊗[R] H') :=
      ((Algebra.TensorProduct.includeRight : H' →ₐ[R] F ⊗[R] H').comp (φ : H →ₐ[R] H')).range
    (Module.Finite R ↥S ∧
    Submodule.span F ((S : Subalgebra R (F ⊗[R] H')) : Set (F ⊗[R] H')) = ⊤ ∧
    (∀ x ∈ S, Coalgebra.comul (R := F) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : (F ⊗[R] H') →ₐ[F] (F ⊗[R] H') ⊗[F] (F ⊗[R] H')).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : (F ⊗[R] H') →ₐ[F] (F ⊗[R] H') ⊗[F] (F ⊗[R] H')).restrictScalars R).comp S.val)).range) ∧
    (∀ x ∈ S, HopfAlgebra.antipode F (A := (F ⊗[R] H')) x ∈ S) ∧
    (∀ x ∈ S, Coalgebra.counit (R := F) (A := (F ⊗[R] H')) x ∈ (algebraMap R F).range)) ∧
    S ≤ (Algebra.TensorProduct.includeRight : H' →ₐ[R] F ⊗[R] H').range := by sorry
