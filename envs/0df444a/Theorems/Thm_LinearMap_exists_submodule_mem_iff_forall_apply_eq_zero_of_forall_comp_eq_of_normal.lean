-- Prove2me | Theorems.Thm_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
-- name    : LinearMap.exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/085c256a-497e-5a07-bfd0-252f6f150f11
-- title:
--   Common kernel of translates of an I-invariant linear form
-- statement:
--   Let $R$ be a commutative ring which is a domain, let $\Gamma$ be a group, and let $T$ be an $R$-module (an additive commutative group with an $R$-module structure). Let $\rho : \Gamma \to \operatorname{End}_R(T)$ be a monoid homomorphism into the $R$-linear endomorphisms of $T$, let $I$ be a subgroup of $\Gamma$ which is assumed normal, and let $f : T \to R$ be an $R$-linear form such that $f \circ \rho(\tau) = f$ for every $\tau \in I$. The assertion is the existence of an $R$-submodule $M \subseteq T$ with the following five properties: (i) for every $x \in T$, one has $x \in M$ if and only if $f(\rho(\gamma)x) = 0$ for all $\gamma \in \Gamma$, so $M$ is exactly the common kernel of all the translates $f \circ \rho(\gamma)$; (ii) $\rho(\gamma)x \in M$ for all $\gamma \in \Gamma$ and all $x \in M$, i.e. $M$ is stable under the action; (iii) $\rho(\tau)x - x \in M$ for every $\tau \in I$ and every $x \in T$, i.e. $I$ acts trivially on $T/M$; (iv) $M$ is saturated: if $r \in R$ is nonzero, $x \in T$ and $r \cdot x \in M$, then $x \in M$; and (v) $f(x) = 0$ for every $x \in M$.
--
--   An elementary piece of linear algebra over a domain, packaging an $I$-invariant linear form into a $\Gamma$-stable saturated submodule on whose quotient $I$ acts trivially. It is used in the passage from decomposition-group to inertia-group invariance for the Tate module of a $p$-divisible group over a ring of integers, being cited by [`PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers`](thm.html#PDivisibleGroup.forall_dual_apply_eq_zero_of_forall_norm_sub_counit_lt_one_of_forall_inertia_of_ringOfIntegers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
    {R : Type*} [CommRing R] [IsDomain R]
    {Γ : Type*} [Group Γ] {T : Type*} [AddCommGroup T] [Module R T]
    (ρ : Γ →* Module.End R T) (I : Subgroup Γ) (hI : I.Normal)
    (f : T →ₗ[R] R) (hf : ∀ τ ∈ I, f ∘ₗ ρ τ = f) :
    ∃ M : Submodule R T,
      (∀ x : T, x ∈ M ↔ ∀ γ : Γ, f (ρ γ x) = 0) ∧
      (∀ (γ : Γ) (x : T), x ∈ M → ρ γ x ∈ M) ∧
      (∀ τ ∈ I, ∀ x : T, ρ τ x - x ∈ M) ∧
      (∀ (r : R) (x : T), r ≠ 0 → r • x ∈ M → x ∈ M) ∧
      (∀ x ∈ M, f x = 0) := by sorry
