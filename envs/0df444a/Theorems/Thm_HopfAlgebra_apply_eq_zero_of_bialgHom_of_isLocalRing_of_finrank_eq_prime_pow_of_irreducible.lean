-- Prove2me | Theorems.Thm_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
-- name    : HopfAlgebra.apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/01d21d25-7228-5ecd-a0c7-e2601d738828
-- title:
--   Points through a local quotient vanish in Galois-invariant p-quotients
-- statement:
--   Let $R$ be a discrete valuation ring of characteristic zero which is a domain, let $p$ be a prime with $p \neq 2$ such that the image of $p$ in $R$ is irreducible (a uniformiser), let $K$ be a fraction field of $R$, and let $L$ be an algebraically closed field that is an algebraic field extension of $K$, with $R$-algebra structure compatible with $K$. Let $M$ be an additive abelian group carrying a distributive action of $\mathrm{Aut}(L/K) = L \simeq_{\mathrm{alg}[K]} L$. Let $H$ be a commutative Hopf $R$-algebra which is finite and free as an $R$-module and cocommutative, with $\mathrm{finrank}_R H = p^a$ for some $a \in \mathbb{N}$. Assume given a bijection $e$ from the set of $R$-algebra homomorphisms $H \to L$, equipped with the convolution monoid structure `WithConv`, onto $M$, such that $e(f \cdot g) = e(f) + e(g)$, and such that whenever $g$ is the pointwise composite $\sigma \circ f$ for $\sigma \in \mathrm{Aut}(L/K)$ one has $e(g) = \sigma \cdot e(f)$. Let $H_0$ be a commutative $R$-bialgebra which is a local ring, and $\pi : H \to H_0$ a homomorphism of $R$-bialgebras. Let $U$ be an additive abelian group with $\mathrm{Nat.card}\,U = p^b$ for some $b \in \mathbb{N}$, and $\varphi : M \to U$ an additive map invariant under the $\mathrm{Aut}(L/K)$-action, i.e. $\varphi(\sigma \cdot m) = \varphi(m)$ for all $\sigma$ and $m$. Then for every $R$-algebra homomorphism $f_0 : H_0 \to L$ one has $\varphi\bigl(e(f_0 \circ \pi)\bigr) = 0$, where $f_0 \circ \pi$ is viewed as an element of the convolution monoid of $R$-algebra homomorphisms $H \to L$.
--
--   This is the Raynaud input to Ribet's level-lowering argument in the case where the absolute ramification index is $1 < p - 1$: when $\mathrm{Spec}\,H_0$ is the connected component of the identity of the finite flat $p$-group $\mathrm{Spec}\,H$, it says that the $L$-points coming from the connected component are killed by every Galois-invariant homomorphism to a finite abelian $p$-group, so that the points of the étale quotient give the largest unramified quotient. It is applied in the construction of the Néron extension attached to the Néron model of $J_0(\cdot)$ at $p$, and it is deduced from the uniqueness-and-factorisation statement [`HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible`](thm.html#HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.apply_eq_zero_of_bialgHom_of_isLocalRing_of_finrank_eq_prime_pow_of_irreducible
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    {M : Type} [AddCommGroup M] [DistribMulAction (L ≃ₐ[K] L) M]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    [Coalgebra.IsCocomm R H] (hrank : ∃ a : ℕ, Module.finrank R H = p ^ a)
    (e : WithConv (H →ₐ[R] L) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : L ≃ₐ[K] L) (f g : WithConv (H →ₐ[R] L)), (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (H₀ : Type) [CommRing H₀] [Bialgebra R H₀] (hloc : IsLocalRing H₀) (π : H →ₐc[R] H₀)
    {U : Type} [AddCommGroup U] (hU : ∃ b : ℕ, Nat.card U = p ^ b)
    (φ : M →+ U) (hφ : ∀ (σ : L ≃ₐ[K] L) (m : M), φ (σ • m) = φ m)
    (f₀ : H₀ →ₐ[R] L) :
    φ (e (WithConv.toConv (f₀.comp (π : H →ₐ[R] H₀)))) = 0 := by sorry
