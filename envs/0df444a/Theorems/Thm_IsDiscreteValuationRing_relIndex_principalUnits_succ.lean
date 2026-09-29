-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_relIndex_principalUnits_succ
-- name    : IsDiscreteValuationRing.relIndex_principalUnits_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/72d7f00b-b52d-5102-ba16-3c8c940e6a5d
-- title:
--   Index of consecutive principal unit groups in a DVR
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, and let $k$ be a natural number with $1 \le k$. For a natural number $n$, write $U^{(n)} =$ `principalUnits R n` for the subgroup of $R^{\times}$ consisting of those units $u$ with $u - 1 \in \mathfrak m^{n}$, where $\mathfrak m$ is the maximal ideal of the local ring $R$ (this set is a subgroup: it contains $1$, and closure under products and inverses follows from $(uv) - 1 = (u-1)v + (v-1)$ and $u^{-1} - 1 = -u^{-1}(u-1)$). The assertion is that the relative index of $U^{(k+1)}$ in $U^{(k)}$, i.e. the index of $U^{(k+1)} \cap U^{(k)} = U^{(k+1)}$ inside $U^{(k)}$, equals the cardinality of the residue field $R/\mathfrak m$ in the sense of `Nat.card`; in particular both sides are $0$ when the residue field is infinite.
--
--   This is the standard computation of the successive quotients of the filtration of the unit group of a discrete valuation ring by principal units, $U^{(k)}/U^{(k+1)} \cong \mathfrak m^{k}/\mathfrak m^{k+1} \cong \kappa$ for $k \ge 1$. It is the inductive step used by [`IsDiscreteValuationRing.relIndex_principalUnits_add`](thm.html#IsDiscreteValuationRing.relIndex_principalUnits_add), which computes $[U^{(k)} : U^{(k+m)}]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_relIndex_principalUnits_succ.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsDiscreteValuationRing.relIndex_principalUnits_succ {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {k : ℕ} (hk : 1 ≤ k) :
    (principalUnits R (k + 1)).relIndex (principalUnits R k) = Nat.card (IsLocalRing.ResidueField R) := by sorry
