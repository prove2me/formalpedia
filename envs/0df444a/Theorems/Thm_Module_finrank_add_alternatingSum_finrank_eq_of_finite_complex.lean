-- Prove2me | Theorems.Thm_Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex
-- name    : Module.finrank_add_alternatingSum_finrank_eq_of_finite_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/aa1de1a2-6ec9-507f-8de6-80748da12202
-- title:
--   Euler characteristic of a bounded complex of finite-dimensional vector spaces
-- statement:
--   Let $k$ be a field and let $K : \mathbb{N} \to \mathrm{Type}$ be a family of $k$-vector spaces, each finite-dimensional over $k$, equipped with $k$-linear maps $\delta_i : K_i \to K_{i+1}$ satisfying $\delta_{i+1} \circ \delta_i = 0$ for all $i$. Let $n$ be a natural number such that $K_i$ is a subsingleton (i.e. zero) for every $i > n$. Let $H_0$ be a $k$-vector space given together with a $k$-linear isomorphism $e_0 : H_0 \cong \ker \delta_0$, and let $H : \mathbb{N} \to \mathrm{Type}$ be a family of $k$-vector spaces given together with $k$-linear maps $\pi_i : \ker \delta_{i+1} \to H_i$ that are surjective and whose kernels are exactly the preimage of $\operatorname{im} \delta_i$ under the inclusion $\ker \delta_{i+1} \hookrightarrow K_{i+1}$; thus $H_i$ presents the cohomology $\ker \delta_{i+1} / \operatorname{im} \delta_i$ in degree $i+1$, and $H_0$ presents $\ker \delta_0$. The conclusion is the identity of integers $$\dim_k H_0 + \sum_{i=0}^{n-1} (-1)^{i+1} \dim_k H_i = \sum_{i=0}^{n} (-1)^i \dim_k K_i,$$ the sums being over `Finset.range n` and `Finset.range (n+1)` respectively, with all dimensions taken as `Module.finrank` cast to $\mathbb{Z}$. Note that the cohomology spaces $H_i$ are not assumed finite-dimensional: this follows from the hypotheses.
--
--   This is the Euler–Poincaré principle for a cochain complex of finite-dimensional vector spaces concentrated in degrees $0,\dots,n$: the alternating sum of the dimensions of the cohomology equals the alternating sum of the dimensions of the terms. The cohomology is taken in presented form (a space with a chosen isomorphism, respectively a chosen surjection with prescribed kernel) so that it can be applied to complexes whose cohomology is realised by concrete modules; it is used in [`Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing`](thm.html#Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing), where the complex is a base change of a finite free complex over a local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.finrank_add_alternatingSum_finrank_eq_of_finite_complex
    (k : Type u) [Field k]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module k (K i)] [∀ i, Module.Finite k (K i)]
    (δ : ∀ i, K i →ₗ[k] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (K i))
    (H0 : Type u) [AddCommGroup H0] [Module k H0] (e₀ : H0 ≃ₗ[k] LinearMap.ker (δ 0))
    (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module k (H i)]
    (π : ∀ i, LinearMap.ker (δ (i + 1)) →ₗ[k] H i) (hπ : ∀ i, Function.Surjective (π i))
    (hπker : ∀ i, LinearMap.ker (π i) =
      (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) :
    (Module.finrank k H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank k (H i) : ℤ) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank k (K i) : ℤ) := by sorry
