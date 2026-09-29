-- Prove2me | Theorems.Thm_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq
-- name    : IsLocalRing.exists_mem_principalUnits_coe_sub_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/f4ab4b01-b985-563a-a506-81fa0e8840aa
-- title:
--   Elements of 𝔪^k are u-1 for u in the k-th principal unit group
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m =$ `maximalIdeal R`, let $k$ be a natural number with $1 \le k$, and let $x \in R$ lie in $\mathfrak m^k$. The assertion is that there is a unit $u \in R^\times$ belonging to the subgroup `principalUnits R k` — by definition the set of units $u$ with $(u : R) - 1 \in \mathfrak m^k$, which is a subgroup of $R^\times$ — such that the image of $u$ in $R$ satisfies $u - 1 = x$. Thus the map $u \mapsto u - 1$ from `principalUnits R k` to $\mathfrak m^k$ is surjective for $k \ge 1$; equivalently, $1 + x$ is a unit of $R$ for every $x \in \mathfrak m^k$ with $k \ge 1$, and that unit lies in the $k$-th principal unit group. No Noetherian, discrete valuation or completeness hypothesis is imposed; only that $R$ is a commutative local ring.
--
--   This is the surjectivity half of the standard identification $U^{(k)}/U^{(k+1)} \cong \mathfrak m^k/\mathfrak m^{k+1}$ for $k \ge 1$ in the filtration of the unit group of a local ring by principal units. It is used in computing the graded pieces of that filtration, in particular for the relative index of `principalUnits` in consecutive degrees over a discrete valuation ring and for a rank computation for invariants of homomorphism groups attached to principal units modulo powers of the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsLocalRing.exists_mem_principalUnits_coe_sub_one_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} (hk : 1 ≤ k) {x : R} (hx : x ∈ maximalIdeal R ^ k) :
    ∃ u ∈ principalUnits R k, (u : R) - 1 = x := by sorry
