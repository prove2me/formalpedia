-- Prove2me | Theorems.Thm_IsGalois_exists_basis_baseChange_forall_apply_eq_self
-- name    : IsGalois.exists_basis_baseChange_forall_apply_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/ecefadfd-7dd5-522b-8deb-e4d6526da018
-- title:
--   Speiser's theorem: invariant L-basis for semilinear Galois actions
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a finite-dimensional Galois extension of $K$, and let $U$ be a finite-dimensional $K$-vector space. Let $\rho$ be a monoid homomorphism from the Galois group $L \simeq_{\mathrm{alg}[K]} L$ to the monoid of $K$-linear endomorphisms of $U$ under composition, so that each $\rho(\sigma)$ is an invertible $K$-linear automorphism of $U$. Let $f$ assign to each $\sigma$ in the Galois group an additive endomorphism $f(\sigma)$ of $L \otimes_K U$, and assume that on pure tensors these are given by the diagonal formula $f(\sigma)(l \otimes_K u) = \sigma(l) \otimes_K \rho(\sigma)(u)$ for all $l \in L$ and $u \in U$; this condition determines $f(\sigma)$ and makes it $\sigma$-semilinear over $L$. The conclusion asserts the existence of a basis $b$ of $L \otimes_K U$ as an $L$-module, indexed by $\mathrm{Fin}(\operatorname{finrank}_K U)$, all of whose members are invariant: $f(\sigma)(b_i) = b_i$ for every $\sigma$ in the Galois group and every index $i$. No multiplicativity of $\sigma \mapsto f(\sigma)$ is hypothesised; it follows from the formula on pure tensors.
--
--   This is Speiser's extension of Hilbert's Theorem 90 from $\mathrm{GL}_1$ to $\mathrm{GL}_n$, in the shape used for Galois descent of vector spaces carrying a semilinear action: a semilinear representation obtained by base change is trivialised by an invariant $L$-basis, equivalently $H^1(\mathrm{Gal}(L/K), \mathrm{GL}_n(L)) = 1$. It is used in the construction of simultaneous eigenvectors for a family of commuting operators fixed by a fixing subgroup, in [`PadicComplex.exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup`](thm.html#PadicComplex.exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGalois_exists_basis_baseChange_forall_apply_eq_self.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IsGalois.exists_basis_baseChange_forall_apply_eq_self
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i := by sorry
