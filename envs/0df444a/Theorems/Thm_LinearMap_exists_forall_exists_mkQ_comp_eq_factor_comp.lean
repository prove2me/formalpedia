-- Prove2me | Theorems.Thm_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp
-- name    : LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/03c2f1c5-05b3-5dc6-acd5-802f9877906d
-- title:
--   Uniform Artin–Rees lifting of maps into N/IⁿN
-- statement:
--   Let $B$ be a commutative Noetherian ring and $I \subseteq B$ an ideal, and let $M$ and $N$ be $B$-modules that are finite (finitely generated) as $B$-modules. The assertion is that there is a natural number $c$, depending only on $B$, $I$, $M$ and $N$, with the following property: for every natural number $n$ and every $B$-linear map $f : M \to N/(I^{n+c} \cdot \top)$, where $I^{n+c} \cdot \top$ denotes the submodule $I^{n+c}N$ of $N$ obtained by scaling the top submodule, there exists a $B$-linear map $g : M \to N$ such that the composite of $g$ with the quotient map $N \to N/(I^{n}\cdot\top)$ equals the composite of $f$ with the map $N/(I^{n+c}\cdot\top) \to N/(I^{n}\cdot\top)$ induced (via `Submodule.factor`) by the inclusion $I^{n+c}N \subseteq I^{n}N$ coming from $I^{n+c} \subseteq I^{n}$. Equivalently, $g(m) \equiv f(m) \bmod I^{n}N$ for all $m \in M$; the point is that the single constant $c$ works simultaneously for all $n$ and all $f$.
--
--   This is the uniform Artin–Rees statement that a homomorphism into $N/I^{n+c}N$ can be corrected, modulo $I^{n}N$, to a homomorphism into $N$ itself, with $c$ independent of $n$. It is the pure commutative-algebra input to the lifting and cocycle-adjustment steps, being cited by [`LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible`](thm.html#LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible) and [`LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top`](thm.html#LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (f : M →ₗ[B] N ⧸ (I ^ (n + c) • (⊤ : Submodule B N))),
      ∃ g : M →ₗ[B] N,
        (I ^ n • (⊤ : Submodule B N)).mkQ ∘ₗ g =
          Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c))) ∘ₗ f := by sorry
