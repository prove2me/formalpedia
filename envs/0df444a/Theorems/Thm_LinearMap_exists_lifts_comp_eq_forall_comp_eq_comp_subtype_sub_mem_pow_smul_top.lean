-- Prove2me | Theorems.Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top
-- name    : LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/60938385-3be2-523d-b3fd-bb5f995a8488
-- title:
--   Compatible lifts of a presentation along a J-adic tower
-- statement:
--   Let $B$ be a Noetherian commutative ring, $J \subseteq B$ an ideal, $G_E$ and $G_K$ be $B$-modules with $G_K$ finitely generated, and let $p \colon B^r \to G_E$ be $B$-linear, where $B^r$ denotes $\mathrm{Fin}\,r \to B$. Suppose given families of $B$-modules $F_k$, $E_k$ ($k \in \mathbb{N}$) together with $B$-linear maps $\varphi_k \colon F_{k+1} \to F_k$, surjective, with $\ker \varphi_k = J^{k+1} F_{k+1}$; maps $\tau_k \colon E_{k+1} \to E_k$ with $\ker \tau_k = J^{k+1} E_{k+1}$; surjective maps $\varepsilon_k \colon F_k \to E_k$ with $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$; maps $\psi^E_k \colon G_E \to E_k$ with $\tau_k \circ \psi^E_{k+1} = \psi^E_k$; and maps $\lambda_k \colon G_K \to F_k$ with $\varphi_k \circ \lambda_{k+1} = \lambda_k$ and $\operatorname{range} \lambda_k = \ker \varepsilon_k$; assume finally that for some $c \in \mathbb{N}$ one has $\ker \lambda_{k+c} \subseteq J^{k+1} G_K$ for all $k$. Then there exist $B$-linear maps $\ell_n \colon B^r \to F_n$ and $\delta_n \colon \ker p \to G_K$, for all $n \in \mathbb{N}$, such that $\varepsilon_n \circ \ell_n = \psi^E_n \circ p$, $\varphi_n \circ \ell_{n+1} = \ell_n$, $\lambda_n \circ \delta_n$ equals the restriction of $\ell_n$ to the submodule $\ker p$, and $\delta_{n+1} - \delta_n \in J^{n+1} \cdot \operatorname{Hom}_B(\ker p, G_K)$ for every $n$.
--
--   This is a one-chart approximation statement of Artin–Rees type: a presentation $p$ of a module is lifted compatibly through a tower of $J$-adic truncations, and the resulting classes of the relations submodule $\ker p$ are represented by a sequence of homomorphisms into $G_K$ that is Cauchy for the $J$-adic topology on $\operatorname{Hom}_B(\ker p, G_K)$. It is used in the construction of formal splitting data over an ordered affine cover for a proper morphism over an adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type v} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE)
    (F E : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (τ : ∀ k, E (k + 1) →ₗ[B] E k)
    (hτk : ∀ k, LinearMap.ker (τ k) = J ^ (k + 1) • (⊤ : Submodule B (E (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (hεs : ∀ k, Function.Surjective (ε k))
    (hεc : ∀ k, τ k ∘ₗ ε (k + 1) = ε k ∘ₗ φ k)
    (ψE : ∀ k, GE →ₗ[B] E k) (hψEc : ∀ k, τ k ∘ₗ ψE (k + 1) = ψE k)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (hlami : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (lam (k + c)) ≤ J ^ (k + 1) • (⊤ : Submodule B GK)) :
    ∃ (ℓ : ∀ n : ℕ, (Fin r → B) →ₗ[B] F n) (δs : ∀ n : ℕ, ↥(LinearMap.ker p) →ₗ[B] GK),
      (∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) ∧
      (∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n) ∧
      (∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype) ∧
      (∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK))) := by sorry
