-- Prove2me | Theorems.Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
-- name    : LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/fa87735c-3795-5baa-b317-2c9ad60ab0ff
-- title:
--   Defect of two compatible comparison maps is I-adically Cauchy
-- statement:
--   Let $B$ be a Noetherian commutative ring and $I \subseteq B$ an ideal. Let $G_K$, $G_E$ be finite $B$-modules and $M$ a $B$-module, and let $\vartheta \colon G_K \to M$, $\theta_E \colon M \to G_E$ be $B$-linear with $\operatorname{range}\vartheta = \ker\theta_E$ and $\theta_E$ surjective. Let $(F_k)_{k \in \mathbb{N}}$ be $B$-modules with transition maps $\varphi_k \colon F_{k+1} \to F_k$ such that $I^{k+1} \cdot F_k = 0$ for all $k$, and let $\lambda_k \colon G_K \to F_k$ satisfy $\varphi_k \circ \lambda_{k+1} = \lambda_k$; assume there is a fixed $c \in \mathbb{N}$ with $\ker\lambda_{k+c} \le I^{k+1} \cdot G_K$ for all $k$. Let $(E_k)_k$ be $B$-modules with maps $\varepsilon_k \colon F_k \to E_k$ such that $\operatorname{range}\lambda_k = \ker\varepsilon_k$. Finally let $\theta_k, \theta'_k \colon M \to F_k$ be two families with $\varphi_k \circ \theta_{k+1} = \theta_k$ and $\varphi_k \circ \theta'_{k+1} = \theta'_k$, with $\theta_k \circ \vartheta = \lambda_k = \theta'_k \circ \vartheta$, and with $\varepsilon_k \circ \theta_k = \varepsilon_k \circ \theta'_k$ for all $k$. Then there exists a sequence $g \colon \mathbb{N} \to \operatorname{Hom}_B(G_E, G_K)$ such that $g_{k+1} - g_k \in I^{k+1} \cdot \operatorname{Hom}_B(G_E,G_K)$ and $\theta'_k - \theta_k = \lambda_k \circ g_k \circ \theta_E$ for every $k$.
--
--   This is the per-level comparison step in an $I$-adic descent argument: two families of comparison maps out of $M$ that agree on $G_K$ and agree after $\varepsilon_k$ differ by a single $I$-adically Cauchy family of homomorphisms $G_E \to G_K$, which is what allows a limit homomorphism to be extracted. It is used in the construction of the cochain comparing internal-hom data over overlaps of charts, in [`AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {GK : Type v} [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {GE : Type v} [AddCommGroup GE] [Module B GE] [Module.Finite B GE]
    {M : Type v} [AddCommGroup M] [Module B M]
    (ϑ : GK →ₗ[B] M) (θE : M →ₗ[B] GE) (hex : LinearMap.range ϑ = LinearMap.ker θE) (hθE : Function.Surjective θE)
    (F : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hF : ∀ k, I ^ (k + 1) • (⊤ : Submodule B (F k)) = ⊥)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (c : ℕ) (hlami : ∀ k, LinearMap.ker (lam (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule B GK))
    (E : ℕ → Type w) [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (θ θ' : ∀ k, M →ₗ[B] F k)
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k) (hθ'c : ∀ k, φ k ∘ₗ θ' (k + 1) = θ' k)
    (hθϑ : ∀ k, θ k ∘ₗ ϑ = lam k) (hθ'ϑ : ∀ k, θ' k ∘ₗ ϑ = lam k)
    (hθε : ∀ k, ε k ∘ₗ θ k = ε k ∘ₗ θ' k) :
    ∃ g : ℕ → (GE →ₗ[B] GK),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (GE →ₗ[B] GK))) ∧
      (∀ k, θ' k - θ k = lam k ∘ₗ g k ∘ₗ θE) := by sorry
