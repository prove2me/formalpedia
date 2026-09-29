-- Prove2me | Theorems.Thm_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
-- name    : Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/36328afb-ffdb-5ac2-b9ef-858e7132883f
-- title:
--   Uniform Artin–Rees bound for kernels of morphisms of adic systems
-- statement:
--   Let $B$ be a commutative Noetherian ring and $J \subseteq B$ an ideal. Let $(G_k)_{k \in \mathbb{N}}$ and $(F_k)_{k \in \mathbb{N}}$ be families of $B$-modules, with $G_0$ finite over $B$, and suppose given $B$-linear transition maps $\gamma_k : G_{k+1} \to G_k$ and $\varphi_k : F_{k+1} \to F_k$ together with $B$-linear maps $\theta_k : G_k \to F_k$ such that: each $\gamma_k$ is surjective with $\ker \gamma_k = J^{k+1} \cdot G_{k+1}$ (the submodule $J^{k+1} \cdot \top$ of $G_{k+1}$); each $\varphi_k$ satisfies $\ker \varphi_k \subseteq J^{k+1} \cdot F_{k+1}$; each $\theta_k$ is surjective; and the squares commute in the form $\theta_{k+1}$ followed by $\varphi_k$ equals $\gamma_k$ followed by $\theta_k$. The conclusion is that there exists a constant $c \in \mathbb{N}$ such that for all $k, n \in \mathbb{N}$ with $k + c \le n$ one has
--   $$\bigl(J^n \cdot G_n\bigr) \cap \ker \theta_n \subseteq J^k \cdot \ker \theta_n,$$
--   where $J^n \cdot G_n$ denotes $J^n \cdot \top$ in $G_n$ and $J^k \cdot \ker\theta_n$ the $J^k$-multiple of the submodule $\ker \theta_n$. Note that the bound $c$ is uniform: it does not depend on $k$ or $n$.
--
--   This is a uniform Artin–Rees statement for the levelwise kernels $\ker\theta_n$ of a morphism of $J$-adic systems of modules: these kernels need not themselves form an adic system, and the conclusion says that they do so up to a shift by a fixed constant $c$, so that the quotients $\ker\theta_n / J^{k}\ker\theta_n$ stabilise for $n \gg k$. It feeds the construction of the associated adic system of kernels, being used in [`AlgebraicGeometry.OModulePresheaf.exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_range_eq_ker_of_forall_ker_eq_pow_smul_top) and in [`Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top`](thm.html#Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top); the proof invokes Noetherianity of the $J$-adic completion of $B$ via [`AdicCompletion.isNoetherianRing_of_isNoetherianRing`](thm.html#AdicCompletion.isNoetherianRing_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (G : ℕ → Type v) (F : ℕ → Type w)
    [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)] [Module.Finite B (G 0)]
    [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (γ : ∀ k, G (k + 1) →ₗ[B] G k) (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1))))
    (φ : ∀ k, F (k + 1) →ₗ[B] F k)
    (hφk : ∀ k, LinearMap.ker (φ k) ≤ J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (θ : ∀ k, G k →ₗ[B] F k) (hθs : ∀ k, Function.Surjective (θ k))
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      (J ^ n • (⊤ : Submodule B (G n))) ⊓ LinearMap.ker (θ n) ≤ J ^ k • LinearMap.ker (θ n) := by sorry
