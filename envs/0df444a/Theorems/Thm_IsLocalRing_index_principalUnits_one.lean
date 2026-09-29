-- Prove2me | Theorems.Thm_IsLocalRing_index_principalUnits_one
-- name    : IsLocalRing.index_principalUnits_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/541b6008-c013-5868-b8e1-c3b3584dc8fa
-- title:
--   Index of the first principal units subgroup
-- statement:
--   Let $R$ be a commutative local ring, with maximal ideal $\mathfrak m =$ `maximalIdeal R` and residue field `ResidueField R` $= R/\mathfrak m$. For $k \in \mathbb{N}$ the subgroup `principalUnits R k` of $R^\times$ is defined as the set of units $u$ with $u - 1 \in \mathfrak m^{k}$ (a subgroup, since it contains $1$ and is closed under products and inverses). The theorem asserts the equality of natural numbers $$[\,R^\times : \mathrm{principalUnits}\ R\ 1\,] = \#\,(R/\mathfrak m)^\times,$$ where the left-hand side is the subgroup index, i.e. the number of cosets of $\{u \in R^\times : u - 1 \in \mathfrak m\}$ in $R^\times$, and the right-hand side is the cardinality of the unit group of the residue field, both in the `Nat`-valued convention under which an infinite index and an infinite cardinality are recorded as $0$. In particular no finiteness hypothesis on $R$ or on its residue field is imposed; the statement is an identity of natural numbers that reads $0 = 0$ in the infinite case.
--
--   This is the first layer of the unit filtration of a local ring: $R^\times$ modulo the principal units of level $1$ is the unit group of the residue field. It is used in the computation of the index of the subgroup of $k$-th powers in the units of a discrete valuation ring, and in the corresponding index computation for local deformation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_index_principalUnits_one.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsLocalRing.index_principalUnits_one {R : Type*} [CommRing R] [IsLocalRing R] :
    (principalUnits R 1).index = Nat.card (ResidueField R)ˣ := by sorry
