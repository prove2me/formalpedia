-- Prove2me | Theorems.Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
-- name    : Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/347f451b-4441-5b24-86bb-92f70e6a9cf0
-- title:
--   Adic systems: the kernel system is the kernel module's truncation
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I \subseteq R$ an ideal, $M$ and $N$ finite $R$-modules, $K$ an $R$-module, $\rho : M \to N$ an $R$-linear map and $\iota : K \to M$ an injective $R$-linear map whose range is $\ker \rho$ (all modules in one universe). Suppose given: a system $(E_k)_{k \in \mathbb{N}}$ of $R$-modules with $R$-linear maps $\tau_k : E_{k+1} \to E_k$ that are surjective with $\ker \tau_k = I^{k+1} E_{k+1}$; modules $(P_k)$ with maps $\pi_k : P_{k+1} \to P_k$ and surjections $\psi^P_k : M \to P_k$ with $\ker \psi^P_k = I^{k+1} M$ and $\pi_k \circ \psi^P_{k+1} = \psi^P_k$; modules $(C_k)$ with maps $\gamma_k : C_{k+1} \to C_k$ and surjections $\psi^C_k : N \to C_k$ with $\ker \psi^C_k = I^{k+1} N$ and $\gamma_k \circ \psi^C_{k+1} = \psi^C_k$; maps $\theta_k : P_k \to C_k$ with $\theta_k \circ \psi^P_k = \psi^C_k \circ \rho$; and maps $u_k : E_k \to P_k$ with $\pi_k \circ u_{k+1} = u_k \circ \tau_k$, $\operatorname{range} u_k = \ker \theta_k$, and, for some $c \in \mathbb{N}$ and all $k$, $\ker u_{k+c} \subseteq I^{k+1} E_{k+c}$. The conclusion asserts the existence of $R$-linear maps $\psi_k : K \to E_k$ that are all surjective, satisfy $\ker \psi_k = I^{k+1} K$, are compatible in the sense $\tau_k \circ \psi_{k+1} = \psi_k$, and satisfy $u_k \circ \psi_k = \psi^P_k \circ \iota$ for all $k$.
--
--   This identifies an abstract $I$-adic system $(E_k)$ sitting as the kernel of a morphism of truncation systems with the truncation system $(K/I^{k+1}K)$ of the kernel module $K$, compatibly with the inclusion $\iota$; it is the module-theoretic form of the statement that kernels of morphisms of coherent adic systems are again algebraised. It is used in the construction of coherent sheaves on a proper scheme over a complete local base from systems of sheaves on the fibres, via [`AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N K : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [AddCommGroup K] [Module R K]
    (ρ : M →ₗ[R] N) (ι : K →ₗ[R] M) (hι : Function.Injective ι) (hιr : LinearMap.range ι = LinearMap.ker ρ)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (ψP : ∀ k, M →ₗ[R] P k) (hψPs : ∀ k, Function.Surjective (ψP k))
    (hψPk : ∀ k, LinearMap.ker (ψP k) = I ^ (k + 1) • (⊤ : Submodule R M))
    (hψPc : ∀ k, π k ∘ₗ ψP (k + 1) = ψP k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (γ : ∀ k, C (k + 1) →ₗ[R] C k)
    (ψC : ∀ k, N →ₗ[R] C k) (hψCs : ∀ k, Function.Surjective (ψC k))
    (hψCk : ∀ k, LinearMap.ker (ψC k) = I ^ (k + 1) • (⊤ : Submodule R N))
    (hψCc : ∀ k, γ k ∘ₗ ψC (k + 1) = ψC k)
    (θ : ∀ k, P k →ₗ[R] C k) (hθ : ∀ k, θ k ∘ₗ ψP k = ψC k ∘ₗ ρ)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c)))) :
    ∃ ψ : ∀ k, K →ₗ[R] E k,
      (∀ k, Function.Surjective (ψ k)) ∧
      (∀ k, LinearMap.ker (ψ k) = I ^ (k + 1) • (⊤ : Submodule R K)) ∧
      (∀ k, τ k ∘ₗ ψ (k + 1) = ψ k) ∧
      (∀ k, u k ∘ₗ ψ k = ψP k ∘ₗ ι) := by sorry
