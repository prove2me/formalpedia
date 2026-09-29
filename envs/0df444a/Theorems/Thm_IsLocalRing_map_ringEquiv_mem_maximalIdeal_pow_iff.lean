-- Prove2me | Theorems.Thm_IsLocalRing_map_ringEquiv_mem_maximalIdeal_pow_iff
-- name    : IsLocalRing.map_ringEquiv_mem_maximalIdeal_pow_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/2915ef17-7275-56a4-b35b-22b5ec0b0359
-- title:
--   Ring automorphisms preserve powers of the maximal ideal
-- statement:
--   Let $R$ be a commutative ring that is local, with maximal ideal $\mathfrak m =$ `maximalIdeal R` (the ideal of non-units). Let $\sigma : R \simeq_{+*} R$ be a ring automorphism of $R$, let $k$ be a natural number and let $x$ be an element of $R$. The assertion is the equivalence $\sigma(x) \in \mathfrak m^{k} \iff x \in \mathfrak m^{k}$; that is, membership in the $k$-th power of the maximal ideal is invariant under $\sigma$ in both directions, with no restriction on $k$ (the case $k = 0$ being the trivial statement for the unit ideal). Nothing beyond the local ring structure and the automorphism is assumed.
--
--   This is the elementary stability of the filtration $\mathfrak m \supseteq \mathfrak m^2 \supseteq \cdots$ of a local ring under its ring automorphisms, the case of interest being a Galois action on the integers of a local field. It is used in the computation of the dimension of the space of invariants of a homomorphism module built from the principal unit groups $U^{(k)}$, via [`IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank`](thm.html#IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_map_ringEquiv_mem_maximalIdeal_pow_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsLocalRing.map_ringEquiv_mem_maximalIdeal_pow_iff {R : Type*} [CommRing R] [IsLocalRing R]
    (σ : R ≃+* R) {k : ℕ} {x : R} : σ x ∈ maximalIdeal R ^ k ↔ x ∈ maximalIdeal R ^ k := by sorry
