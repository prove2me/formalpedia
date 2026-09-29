-- Prove2me | Theorems.Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
-- name    : Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/18e4aa87-0743-583e-99f4-5e0d31183b25
-- title:
--   Compatible families M → N/Iⁿ⁺¹N come uniquely from widehatHom(M,N)
-- statement:
--   Let $A$ be a commutative Noetherian ring, $I \subseteq A$ an ideal, and let $M$, $N$ be $A$-modules (all in one universe) that are finite as $A$-modules. Suppose given, for every $n : \mathbb{N}$, an $A$-linear map $\psi_n : M \to N/(I^{n+1} \cdot \top)$, and suppose these are compatible with the natural surjections, in the sense that for each $n$ the map $\mathrm{Submodule.factor}$ associated with the inclusion $I^{n+2} \cdot \top \le I^{n+1} \cdot \top$ in $N$, composed after $\psi_{n+1}$, equals $\psi_n$. The conclusion asserts the existence of a unique family $\Phi$ assigning to each $n$ an element $\Phi_n$ of $(M \to_{\ell} N)/(I^{n+1} \cdot \top)$, the quotient of the $A$-module of $A$-linear maps $M \to N$ by $I^{n+1}$ times the whole module, such that: first, the family is compatible with the same truncation maps, $\mathrm{Submodule.factor}(\Phi_{n+1}) = \Phi_n$ for all $n$; and second, for every $n$ and every $A$-linear $g : M \to N$ whose class modulo $I^{n+1} \cdot \top$ equals $\Phi_n$, the composite of $g$ followed by the quotient map $N \to N/(I^{n+1} \cdot \top)$ equals $\psi_n$. Note that the second condition is required of every lift $g$ of $\Phi_n$, and that the indexing runs over the exponents $n+1 \ge 1$.
--
--   This is the statement that the natural map from the $I$-adic completion of $\mathrm{Hom}_A(M,N)$ to $\varprojlim_n \mathrm{Hom}_A(M, N/I^{n+1}N)$ is bijective, for finite modules over a Noetherian ring, expressed concretely in terms of compatible families of truncated homomorphisms rather than of completions. It is used in the construction of morphisms of modules over a formally complete base, being cited in the passage from compatible families of maps on truncations to a single map of presheaves in the proper, adically complete setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (ψ : ∀ n : ℕ, M →ₗ[A] N ⧸ (I ^ (n + 1) • (⊤ : Submodule A N)))
    (hψ : ∀ n : ℕ,
      Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ∘ₗ ψ (n + 1) = ψ n) :
    ∃! Φ : ∀ n : ℕ, (M →ₗ[A] N) ⧸ (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N))),
      (∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (Φ (n + 1)) = Φ n) ∧
      (∀ (n : ℕ) (g : M →ₗ[A] N), Submodule.Quotient.mk g = Φ n →
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N))) ∘ₗ g = ψ n) := by sorry
