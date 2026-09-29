-- Prove2me | Theorems.Thm_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
-- name    : LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/02c56aa8-59f8-5b15-adec-2fb30896d427
-- title:
--   Compatible maps into Artin–Rees quotients lift Cauchy-wise
-- statement:
--   Let $B$ be a commutative Noetherian ring, $I \subseteq B$ an ideal, and let $M$ and $N$ be finite $B$-modules. Let $J : \mathbb{N} \to \{\text{submodules of } N\}$ be a family with $J(k+1) \le J(k)$ for all $k$, sandwiched between the $I$-adic filtration and a shift of it: $I^{k+1} \cdot N \le J(k)$ for all $k$, and, for a fixed natural number $c$, $J(k+c) \le I^{k+1} \cdot N$ for all $k$ (here $I^m \cdot N$ denotes $I^m \bullet \top$, the image of $I^m \otimes N$ in $N$). Let $f(k) : M \to N/J(k)$ be $B$-linear maps, compatible in the sense that for every $k$ the map $f(k+1)$ followed by the canonical projection $N/J(k+1) \to N/J(k)$ induced by $J(k+1) \le J(k)$ equals $f(k)$. Then there is a sequence $g : \mathbb{N} \to \operatorname{Hom}_B(M,N)$ such that for every $k$ the difference $g(k+1) - g(k)$ lies in $I^{k+1} \cdot \operatorname{Hom}_B(M,N)$, and for every $k$ the map $g(k)$ followed by the quotient map $N \to N/J(k)$ equals $f(k)$.
--
--   This is the Artin–Rees bridge between a compatible system of maps into the quotients $N/J(k)$ and a sequence of genuine homomorphisms $M \to N$ that is Cauchy for the $I$-adic topology on $\operatorname{Hom}_B(M,N)$; the filtration $(J(k))$ is only required to be cofinal with the $I$-adic one, with a uniform shift $c$. It is used in the comparison of $\operatorname{Hom}$ and $\operatorname{Ext}^1$ with their $I$-adic completions, and is cited by [`LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq`](thm.html#LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N]
    (J : ℕ → Submodule B N) (hJ : ∀ k, J (k + 1) ≤ J k)
    (hIJ : ∀ k, I ^ (k + 1) • (⊤ : Submodule B N) ≤ J k)
    (c : ℕ) (hJI : ∀ k, J (k + c) ≤ I ^ (k + 1) • (⊤ : Submodule B N))
    (f : ∀ k, M →ₗ[B] N ⧸ J k)
    (hf : ∀ k, Submodule.factor (hJ k) ∘ₗ f (k + 1) = f k) :
    ∃ g : ℕ → (M →ₗ[B] N),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (M →ₗ[B] N))) ∧
      (∀ k, (J k).mkQ ∘ₗ g k = f k) := by sorry
