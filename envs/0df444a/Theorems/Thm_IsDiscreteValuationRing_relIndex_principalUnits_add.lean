-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_relIndex_principalUnits_add
-- name    : IsDiscreteValuationRing.relIndex_principalUnits_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/5e467460-138c-54ef-a0e4-50907d5ac441
-- title:
--   Relative index of principal unit subgroups in a DVR
-- statement:
--   Let $R$ be a commutative ring that is a domain and a discrete valuation ring, with maximal ideal $\mathfrak m$ and residue field $R/\mathfrak m$. For $j \in \mathbb N$, `principalUnits R j` denotes the subgroup of $R^\times$ consisting of those units $u$ with $u - 1 \in \mathfrak m^{j}$ (a subgroup, since the defining condition is stable under multiplication and inversion and contains $1$). The theorem asserts, for every natural number $k$ with $k \ge 1$ and every natural number $n$, the equality
--   $$\bigl[\,\mathrm{principalUnits}\ R\ k : \mathrm{principalUnits}\ R\ (k+n)\,\bigr] = \bigl(\#(R/\mathfrak m)\bigr)^{n},$$
--   where the left-hand side is the relative index `Subgroup.relIndex` of `principalUnits R (k + n)` in `principalUnits R k`, that is, the index of the intersection $\mathrm{principalUnits}\ R\ (k+n) \cap \mathrm{principalUnits}\ R\ k$ inside `principalUnits R k`, and the cardinality on the right is `Nat.card` of the residue field (hence $0$ if the residue field is infinite, in which case the asserted value is $0$ for $n \ge 1$ and $1$ for $n = 0$).
--
--   This is the standard computation of the index of the higher principal unit subgroups $U^{(k)} \supseteq U^{(k+n)}$ of a discrete valuation ring, each successive quotient being isomorphic to the additive group of the residue field. It is used in the computation of indices of unit subgroups attached to local level structures, and in the determination of the index of the image of the $m$-th power map on units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_relIndex_principalUnits_add.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsDiscreteValuationRing.relIndex_principalUnits_add {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (principalUnits R (k + n)).relIndex (principalUnits R k) = Nat.card (IsLocalRing.ResidueField R) ^ n := by sorry
