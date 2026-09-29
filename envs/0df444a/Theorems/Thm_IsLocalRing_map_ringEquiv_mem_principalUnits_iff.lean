-- Prove2me | Theorems.Thm_IsLocalRing_map_ringEquiv_mem_principalUnits_iff
-- name    : IsLocalRing.map_ringEquiv_mem_principalUnits_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/b6c176d7-b6f7-5db4-828d-c7e81f013934
-- title:
--   Ring automorphisms preserve the principal unit filtration
-- statement:
--   Let $R$ be a commutative ring which is local (in the sense of Mathlib's `IsLocalRing`), let $\sigma : R \simeq_{+*} R$ be a ring automorphism of $R$, let $k$ be a natural number and let $u$ be a unit of $R$. Here `principalUnits R k` denotes the subgroup of $R^\times$ consisting of those units $v$ with $v - 1 \in \mathfrak{m}^k$, where $\mathfrak{m}$ is the maximal ideal of $R$ (its closure under multiplication and inversion being part of the definition). The theorem asserts the equivalence: the image of $u$ under the unit group map induced by the multiplicative monoid homomorphism underlying $\sigma$ lies in `principalUnits R k` if and only if $u$ itself lies in `principalUnits R k`. Equivalently, $\sigma(u) - 1 \in \mathfrak{m}^k$ iff $u - 1 \in \mathfrak{m}^k$; so the induced automorphism of $R^\times$ carries the $k$-th principal unit subgroup onto itself, for every $k$ simultaneously, with no hypothesis beyond locality of $R$.
--
--   This is the statement that a ring automorphism of a local ring preserves the maximal ideal and hence each subgroup $U^{(k)} = 1 + \mathfrak{m}^k$ of principal units, i.e. the equivariance of the unit filtration under any group acting on $R$ by ring automorphisms. It is used in the computation of the ranks of the invariants of $\operatorname{Hom}$-modules attached to the filtration quotients, in [`IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank`](thm.html#IsLocalRing.finrank_invariants_linHom_principalUnits_modPow_eq_finrank) and [`IsLocalRing.finrank_invariants_linHom_units_modPow_eq`](thm.html#IsLocalRing.finrank_invariants_linHom_units_modPow_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_map_ringEquiv_mem_principalUnits_iff.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsLocalRing.map_ringEquiv_mem_principalUnits_iff {R : Type*} [CommRing R] [IsLocalRing R]
    (σ : R ≃+* R) {k : ℕ} {u : Rˣ} :
    Units.map (σ : R →* R) u ∈ principalUnits R k ↔ u ∈ principalUnits R k := by sorry
