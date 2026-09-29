-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
-- name    : HopfAlgebra.exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a79253ae-9065-5e48-8588-674f7ec7359d
-- title:
--   Common finite flat model of two generically isomorphic Hopf algebras
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain satisfying `IsDiscreteValuationRing`) and let $K$ be a field which is an $R$-algebra and a fraction field of $R$. Let $H_0$ and $H$ be commutative rings carrying Hopf algebra structures over $R$, each finite and flat as an $R$-module and cocommutative as an $R$-coalgebra. Suppose given an isomorphism $\lambda : K \otimes_R H_0 \to K \otimes_R H$ of $K$-algebras which is compatible with the coalgebra structures over $K$, in the sense that $\mathrm{comul}(\lambda x) = (\lambda \otimes \lambda)(\mathrm{comul}\, x)$ and $\mathrm{counit}(\lambda x) = \mathrm{counit}\, x$ for all $x \in K \otimes_R H_0$. The conclusion asserts the existence of a commutative ring $C$ with a Hopf algebra structure over $R$, finite and flat as an $R$-module and cocommutative, together with two $R$-bialgebra homomorphisms $j_0 : H_0 \to C$ and $j : H \to C$, such that $j_0$ and $j$ are injective, the base-changed $K$-linear maps $K \otimes_R H_0 \to K \otimes_R C$ and $K \otimes_R H \to K \otimes_R C$ induced by $j_0$ and $j$ are surjective, and the two embeddings agree on the generic fibre through $\lambda$: for every $y \in H_0$ one has $1 \otimes j_0(y) = (\mathrm{id}_K \otimes j)(\lambda(1 \otimes y))$ in $K \otimes_R C$.
--
--   This is the Hopf-algebra form of the construction of a common finite flat model dominating two finite flat models of the same finite commutative group scheme over the generic point, obtained classically as the schematic closure of the graph of the generic isomorphism. It is used in the comparison of finite flat models arising from torsion of modular curves, being cited by [`ModularCurve.exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero`](thm.html#ModularCurve.exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open scoped TensorProduct in

theorem HopfAlgebra.exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H₀ : Type v} [CommRing H₀] [HopfAlgebra R H₀] [Module.Finite R H₀] [Module.Flat R H₀]
    [Coalgebra.IsCocomm R H₀]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    (lam : (K ⊗[R] H₀) ≃ₐ[K] (K ⊗[R] H))
    (hlam_comul : ∀ x, Coalgebra.comul (R := K) (lam x) =
      (TensorProduct.map lam.toLinearMap lam.toLinearMap) (Coalgebra.comul (R := K) x))
    (hlam_counit : ∀ x, Coalgebra.counit (R := K) (lam x) = Coalgebra.counit (R := K) x) :
    ∃ (C : Type v) (_ : CommRing C) (_ : HopfAlgebra R C) (_ : Module.Finite R C)
      (_ : Module.Flat R C) (_ : Coalgebra.IsCocomm R C)
      (j₀ : H₀ →ₐc[R] C) (j : H →ₐc[R] C),
      Function.Injective j₀ ∧ Function.Injective j ∧
      Function.Surjective ((j₀ : H₀ →ₐ[R] C).toLinearMap.baseChange K) ∧
      Function.Surjective ((j : H →ₐ[R] C).toLinearMap.baseChange K) ∧
      ∀ y : H₀, (1 : K) ⊗ₜ[R] (j₀ y) =
        ((j : H →ₐ[R] C).toLinearMap.baseChange K) (lam ((1 : K) ⊗ₜ[R] y)) := by sorry
