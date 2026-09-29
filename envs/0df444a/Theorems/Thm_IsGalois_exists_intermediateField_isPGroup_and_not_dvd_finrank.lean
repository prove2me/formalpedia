-- Prove2me | Theorems.Thm_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank
-- name    : IsGalois.exists_intermediateField_isPGroup_and_not_dvd_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/659c9c48-4d64-5f2d-af7f-2d76b0061e7f
-- title:
--   Existence of a p-group layer of index prime to p
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra, finite-dimensional over $k$ and Galois over $k$, and let $p$ be a prime. The assertion is that there exists an intermediate field $E$ of $K/k$ such that the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$ — that is, $\mathrm{Gal}(K/E)$ — is a $p$-group in the sense of `IsPGroup p`, and such that $p$ does not divide the $k$-dimension $[E:k] = \mathrm{finrank}_k E$. No bound on $[K:E]$ or on $[E:k]$ beyond these two conditions is asserted, and $E$ is produced non-constructively (as an existential witness); the statement is for an arbitrary base field $k$, with no separability or characteristic restriction beyond what `IsGalois k K` already provides.
--
--   This is the standard Galois-theoretic reformulation of Sylow's existence theorem: the fixed field of a Sylow $p$-subgroup of $\mathrm{Gal}(K/k)$ is an intermediate field of degree prime to $p$ over which $K$ is a $p$-extension. It serves as the base for a $p$-group layer in the Galois-cohomological arguments, where restriction to a subgroup of index prime to $p$ is injective on $p$-primary cohomology; it is used by [`groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two`](thm.html#groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGalois_exists_intermediateField_isPGroup_and_not_dvd_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem IsGalois.exists_intermediateField_isPGroup_and_not_dvd_finrank
    (k K : Type*) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] :
    ∃ E : IntermediateField k K, IsPGroup p (K ≃ₐ[↥E] K) ∧ ¬ p ∣ Module.finrank k ↥E := by sorry
