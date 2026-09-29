-- Prove2me | Theorems.Thm_LinearEquiv_exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq
-- name    : LinearEquiv.exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/18173983-1d8f-5807-8be6-712bf4a0cad0
-- title:
--   Equivariant dual isomorphism descends to the modules
-- statement:
--   Let $R$ be a commutative ring, $k$ a commutative $R$-algebra, and let $\Omega$ and $S$ be $R$-modules that are finite and free. Let $\iota$ be an index type and let $a \colon \iota \to \operatorname{End}_R(\Omega)$ and $s \colon \iota \to \operatorname{End}_R(S)$ be families of $R$-linear endomorphisms. Suppose $\tau \colon \operatorname{Hom}_R(\Omega,R) \xrightarrow{\sim} \operatorname{Hom}_R(S,R)$ is an $R$-linear isomorphism of dual modules which intertwines the transposed families, that is, $\tau(D \circ a_t) = \tau(D) \circ s_t$ for every $t \in \iota$ and every linear form $D$ on $\Omega$. The conclusion asserts the existence of an $R$-linear isomorphism $\theta \colon \Omega \xrightarrow{\sim} S$ such that, first, $\tau(D) = D \circ \theta^{-1}$ for every linear form $D$ on $\Omega$; second, $\theta \circ a_t = s_t \circ \theta$ as $R$-linear maps $\Omega \to S$ for every $t \in \iota$; and third, the existence of a $k$-linear isomorphism $\Xi \colon k \otimes_R \Omega \xrightarrow{\sim} k \otimes_R S$ satisfying $\Xi(c \otimes x) = c \otimes \theta(x)$ for all $c \in k$, $x \in \Omega$, and $\Xi \circ (a_t \otimes_R k) = (s_t \otimes_R k) \circ \Xi$ for every $t \in \iota$, where the base-changed maps are the $k$-linear extensions of $a_t$ and $s_t$.
--
--   This is the linear-algebra statement that, for finite free modules, an isomorphism between dual modules equivariant for transposed endomorphism families is the transpose of an equivariant isomorphism of the modules themselves, together with its base change along $R \to k$. It is used in the identification of the cotangent space of a modular-curve model with a lattice of modular forms compatible with Hecke operators, via [`ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq`](thm.html#ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearEquiv_exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LinearEquiv.exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq
    (R : Type*) [CommRing R] (k : Type*) [CommRing k] [Algebra R k]
    (Ω : Type*) [AddCommGroup Ω] [Module R Ω] [Module.Finite R Ω] [Module.Free R Ω]
    (S : Type*) [AddCommGroup S] [Module R S] [Module.Finite R S] [Module.Free R S]
    {ι : Type*} (a : ι → (Ω →ₗ[R] Ω)) (s : ι → (S →ₗ[R] S))
    (τ : Module.Dual R Ω ≃ₗ[R] Module.Dual R S)
    (hτ : ∀ (t : ι) (D : Module.Dual R Ω), τ (D ∘ₗ a t) = (τ D) ∘ₗ s t) :
    ∃ θ : Ω ≃ₗ[R] S,
      (∀ D : Module.Dual R Ω, τ D = D ∘ₗ (θ.symm : S →ₗ[R] Ω)) ∧
      (∀ t : ι, (θ : Ω →ₗ[R] S) ∘ₗ a t = s t ∘ₗ (θ : Ω →ₗ[R] S)) ∧
      ∃ Ξ : k ⊗[R] Ω ≃ₗ[k] k ⊗[R] S,
        (∀ (c : k) (x : Ω), Ξ (c ⊗ₜ x) = c ⊗ₜ θ x) ∧
        ∀ t : ι, (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S) ∘ₗ (a t).baseChange k =
          (s t).baseChange k ∘ₗ (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S) := by sorry
