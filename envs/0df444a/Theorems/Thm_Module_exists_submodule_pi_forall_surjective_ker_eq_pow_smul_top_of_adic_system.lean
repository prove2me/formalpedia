-- Prove2me | Theorems.Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
-- name    : Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/d4828738-0f0c-5226-a0a8-cccba3ee43e5
-- title:
--   Inverse limit of an I-adic system of modules
-- statement:
--   Let $R$ be a commutative ring and $I \subseteq R$ an ideal that is finitely generated. Let $(E_k)_{k \in \mathbb{N}}$ be a family of $R$-modules (all in a single universe), and for each $k$ let $\tau_k : E_{k+1} \to E_k$ be an $R$-linear map. Assume every $\tau_k$ is surjective and that its kernel is exactly $I^{k+1} \cdot E_{k+1}$, i.e. the submodule $I^{k+1} \bullet \top$ of $E_{k+1}$. The assertion is that there is an $R$-submodule $L$ of the product $\prod_k E_k$ with the following three properties. First, $L$ is precisely the submodule of compatible families: a family $e$ lies in $L$ if and only if $\tau_k(e_{k+1}) = e_k$ for all $k$, so $L$ is the inverse limit $\varprojlim_k E_k$ realised inside the product. Second, for each $k$ the $R$-linear map $L \to E_k$ obtained by composing the inclusion of $L$ into the product with the $k$-th coordinate projection is surjective. Third, for each $k$ the kernel of that map $L \to E_k$ equals $I^{k+1} \cdot L$, i.e. $I^{k+1} \bullet \top$ as a submodule of $L$. No finiteness hypothesis is imposed on the modules $E_k$.
--
--   This is the standard statement that an $I$-adic inverse system over a finitely generated ideal is induced by its limit: the limit module $L$ surjects onto each level with kernel the $(k+1)$-st adic power, so that $E_k \cong L/I^{k+1}L$. It is used by [`Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`](thm.html#Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker), where such a system is produced from a presentation by ranges and kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1)))) :
    ∃ L : Submodule R (∀ k, E k),
      (∀ e : ∀ k, E k, e ∈ L ↔ ∀ k, τ k (e (k + 1)) = e k) ∧
      (∀ k, Function.Surjective ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k)) ∧
      (∀ k, LinearMap.ker ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k) =
        I ^ (k + 1) • (⊤ : Submodule R L)) := by sorry
