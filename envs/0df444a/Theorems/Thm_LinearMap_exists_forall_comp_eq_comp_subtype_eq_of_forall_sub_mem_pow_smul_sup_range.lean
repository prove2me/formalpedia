-- Prove2me | Theorems.Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
-- name    : LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/0bca4954-9401-5406-9ad5-58d899fbde98
-- title:
--   Coherent lifts with prescribed restriction to the relation module
-- statement:
--   Let $B$ be a commutative Noetherian ring and $J \subseteq B$ an ideal, let $G_E$ and $G_K$ be $B$-modules with $G_K$ finitely generated, and let $p \colon B^r \to G_E$ be a surjective $B$-linear map, $r \in \mathbb{N}$; write $S = \ker p$. Let $F_k$, $E_k$ ($k \in \mathbb{N}$) be $B$-modules equipped with $B$-linear maps $\varphi_k \colon F_{k+1} \to F_k$ that are surjective with $\ker \varphi_k = J^{k+1} F_{k+1}$, maps $\varepsilon_k \colon F_k \to E_k$, $\psi^E_k \colon G_E \to E_k$ and $\lambda_k \colon G_K \to F_k$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$ and $\operatorname{range} \lambda_k = \ker \varepsilon_k$. Assume given a compatible family $\ell_n \colon B^r \to F_n$ with $\varepsilon_n \circ \ell_n = \psi^E_n \circ p$ and $\varphi_n \circ \ell_{n+1} = \ell_n$; maps $\delta_n \colon S \to G_K$ with $\lambda_n \circ \delta_n = \ell_n|_S$ and $\delta_{n+1} - \delta_n \in J^{n+1} \operatorname{Hom}_B(S, G_K)$; and a single $\delta \colon S \to G_K$ such that for every $n$, $\delta - \delta_n$ lies in the sum of $J^{n+1} \operatorname{Hom}_B(S, G_K)$ and the image of the restriction map $\operatorname{Hom}_B(B^r, G_K) \to \operatorname{Hom}_B(S, G_K)$, $g \mapsto g|_S$. Then there exists a family $\ell'_k \colon B^r \to F_k$ with $\varphi_k \circ \ell'_{k+1} = \ell'_k$, $\varepsilon_k \circ \ell'_k = \psi^E_k \circ p$ and $\ell'_k|_S = \lambda_k \circ \delta$ for all $k$.
--
--   This is a purely module-theoretic lemma of Artin–Rees type: the levelwise correction of a compatible family of lifts so that its restriction to the relation module $\ker p$ becomes exactly the prescribed map $\delta$, coherently in the level $k$. It is used in the construction of chart data for $\mathcal{O}$-module presheaves over an adically complete base, where the $F_k$ form the tower of truncations of a formal extension and $\delta$ records the splitting defect.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type u} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE) (hp : Function.Surjective p)
    (F E : ℕ → Type u) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))

    (ℓ : ∀ n, (Fin r → B) →ₗ[B] F n) (hℓε : ∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) (hℓφ : ∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n)
    (δs : ∀ n, ↥(LinearMap.ker p) →ₗ[B] GK) (hδs : ∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype)
    (hδsc : ∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)))

    (δ : ↥(LinearMap.ker p) →ₗ[B] GK)
    (hδ : ∀ n, δ - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)) ⊔
      LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker p).subtype)) :
    ∃ ℓ' : ∀ k, (Fin r → B) →ₗ[B] F k,
      (∀ k, φ k ∘ₗ ℓ' (k + 1) = ℓ' k) ∧
      (∀ k, ε k ∘ₗ ℓ' k = ψE k ∘ₗ p) ∧
      (∀ k, ℓ' k ∘ₗ (LinearMap.ker p).subtype = lam k ∘ₗ δ) := by sorry
