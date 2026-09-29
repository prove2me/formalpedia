-- Prove2me | Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
-- name    : HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/394992c6-1182-529b-b41f-e44a9153a592
-- title:
--   Raynaud full faithfulness in morphism form, p≠ 2
-- statement:
--   Let $R$ be a discrete valuation domain of characteristic $0$, let $p$ be a prime with $p \neq 2$ which is irreducible in $R$ (a uniformiser), let $K$ be a fraction field of $R$, and let $L$ be an algebraically closed field which is an algebraic extension of $K$, with the $R$-algebra structure on $L$ compatible with that of $K$. Let $M_1, M_2$ be abelian groups carrying distributive actions of the group $\mathrm{Aut}(L/K)$ of $K$-algebra automorphisms of $L$. Let $H_1$ be a commutative $R$-algebra with a cocommutative Hopf $R$-algebra structure, finite and free as an $R$-module, of rank $p^{a}$ for some $a \in \mathbb{N}$, and let $e_1$ be a bijection from the set of $R$-algebra maps $H_1 \to L$, viewed with its convolution monoid structure, onto $M_1$, which takes convolution products to sums and which is equivariant in the sense that whenever $\sigma \in \mathrm{Aut}(L/K)$ and $g(x) = \sigma(f(x))$ for all $x \in H_1$, one has $e_1(g) = \sigma \cdot e_1(f)$; let $H_2, e_2$ satisfy the same hypotheses. Then for every additive, $\mathrm{Aut}(L/K)$-equivariant map $\varphi \colon M_1 \to M_2$ there is exactly one $R$-bialgebra homomorphism $g \colon H_2 \to H_1$ such that $e_2(f \circ g) = \varphi(e_1(f))$ for every $R$-algebra map $f \colon H_1 \to L$.
--
--   This is Raynaud's full faithfulness theorem in morphism form over an absolutely unramified discrete valuation ring with $p \neq 2$: finite flat commutative group schemes of $p$-power order over $R$ are determined, together with their morphisms, by the $\mathrm{Aut}(L/K)$-module of their $L$-points. It is used in the passage from Galois-module maps to maps of Néron models of $J_0$ and in the localisation statements built on it, and it is obtained here from full faithfulness over the fraction field of characteristic zero, the bound $f^{\operatorname{rank}_R H} = 1$ on convolution powers of points of a finite free cocommutative Hopf algebra, and descent of a bialgebra map from the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (L ≃ₐ[K] L) M₁] [DistribMulAction (L ≃ₐ[K] L) M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra R H₁] [Module.Finite R H₁] [Module.Free R H₁]
    [Coalgebra.IsCocomm R H₁] (hrank₁ : ∃ a : ℕ, Module.finrank R H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[R] L) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H₁ →ₐ[R] L)), (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
    (H₂ : Type) [CommRing H₂] [HopfAlgebra R H₂] [Module.Finite R H₂] [Module.Free R H₂]
    [Coalgebra.IsCocomm R H₂] (hrank₂ : ∃ a : ℕ, Module.finrank R H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[R] L) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H₂ →ₐ[R] L)), (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
    (φ : M₁ →+ M₂)
    (hφ : ∀ (σ : L ≃ₐ[K] L) (m : M₁), φ (σ • m) = σ • φ m) :
    ∃! g : H₂ →ₐc[R] H₁,
      ∀ f : WithConv (H₁ →ₐ[R] L),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[R] H₁))) = φ (e₁ f) := by sorry
