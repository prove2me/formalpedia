-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_model_prod
-- name    : HopfAlgebra.exists_finiteFlat_model_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/da8947e6-edfa-5c73-8081-7669421a9ece
-- title:
--   Tensor product model for a product of Galois modules
-- statement:
--   Let $R$ be a commutative ring, $L$ a commutative $R$-algebra, and $\Gamma$ a group acting on $L$ by ring automorphisms in a way compatible with the $R$-action (so that $\Gamma$ acts by $R$-algebra automorphisms), and let $M_1, M_2$ be abelian groups carrying additive $\Gamma$-actions. Suppose given commutative rings $H_1$ and $H_2$, each equipped with a Hopf algebra structure over $R$, each finite and flat as an $R$-module and with cocommutative comultiplication, and for $i = 1,2$ a bijection $e_i$ from $\mathrm{Hom}_{R\text{-alg}}(H_i, L)$, regarded through `WithConv` as a monoid under convolution, onto $M_i$, such that $e_i(f * g) = e_i f + e_i g$ for all $f, g$, and such that for every $\sigma \in \Gamma$ and all $f, g$ with $g(x) = \sigma \cdot f(x)$ for all $x \in H_i$ one has $e_i g = \sigma \cdot e_i f$. The conclusion asserts the existence of a type $H$ with a commutative ring structure and an $R$-Hopf algebra structure, finite and flat over $R$ and cocommutative, together with a bijection $e$ from $\mathrm{Hom}_{R\text{-alg}}(H, L)$ under convolution onto $M_1 \times M_2$ satisfying the same two properties: $e(f * g) = e f + e g$, and $e g = \sigma \cdot e f$ whenever $g$ is the pointwise $\sigma$-twist of $f$, for the componentwise $\Gamma$-action on $M_1 \times M_2$.
--
--   This is the Hopf-algebra form of the statement that the product of two finite flat commutative group schemes represents the product of their point functors: a model for $M_1$ and a model for $M_2$ yield a model for $M_1 \times M_2$. It is used in the construction of finite flat models for the modules attached to cocycles, being cited by [`ResidualGaloisRep.isLocallyFlatCocycleAd_add`](thm.html#ResidualGaloisRep.isLocallyFlatCocycleAd_add) and [`ResidualGaloisRep.isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle`](thm.html#ResidualGaloisRep.isLocallyFlatCocycleAd_zero_of_isLocallyFlatCocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_model_prod.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfAlgebra.exists_finiteFlat_model_prod
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    {Γ : Type} [Group Γ] [MulSemiringAction Γ L] [SMulCommClass Γ R L]
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [DistribMulAction Γ M₁] [DistribMulAction Γ M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra R H₁] [Module.Finite R H₁] [Module.Flat R H₁]
    [Coalgebra.IsCocomm R H₁]
    (e₁ : WithConv (H₁ →ₐ[R] L) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : Γ) (f g : WithConv (H₁ →ₐ[R] L)), (∀ x : H₁, g x = σ • (f x)) → e₁ g = σ • (e₁ f))
    (H₂ : Type) [CommRing H₂] [HopfAlgebra R H₂] [Module.Finite R H₂] [Module.Flat R H₂]
    [Coalgebra.IsCocomm R H₂]
    (e₂ : WithConv (H₂ →ₐ[R] L) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : Γ) (f g : WithConv (H₂ →ₐ[R] L)), (∀ x : H₂, g x = σ • (f x)) → e₂ g = σ • (e₂ f)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : WithConv (H →ₐ[R] L) ≃ M₁ × M₂,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : Γ) (f g : WithConv (H →ₐ[R] L)), (∀ x : H, g x = σ • (f x)) → e g = σ • (e f) := by sorry
