-- Prove2me | Theorems.Thm_IsLocalRing_principalUnits_one_eq_ker_map_residue
-- name    : IsLocalRing.principalUnits_one_eq_ker_map_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/67babb64-8148-5c57-9e0d-e9d605785359
-- title:
--   Principal units of level one are the kernel of reduction
-- statement:
--   Let $R$ be a commutative ring that is local, with maximal ideal $\mathfrak{m}$ and residue field $\mathrm{ResidueField}\,R = R/\mathfrak{m}$. For a natural number $k$, the subgroup $\mathtt{principalUnits}\ R\ k$ of $R^\times$ is defined to consist of those units $u$ whose image in $R$ satisfies $u - 1 \in \mathfrak{m}^k$ (closure under multiplication and inverses coming from the identities $uv - 1 = (u-1)v + (v-1)$ and $u^{-1} - 1 = -u^{-1}(u-1)$). The theorem asserts the equality of subgroups of $R^\times$
--   $$\mathtt{principalUnits}\ R\ 1 = \ker\bigl(\mathrm{Units.map}(\mathtt{residue}\ R)\bigr),$$
--   where $\mathtt{residue}\ R : R \to R/\mathfrak{m}$ is the quotient map, viewed as a monoid homomorphism, and $\mathrm{Units.map}$ is the induced homomorphism $R^\times \to (R/\mathfrak{m})^\times$. Thus a unit $u$ of $R$ satisfies $u - 1 \in \mathfrak{m}$ if and only if its image in $(R/\mathfrak{m})^\times$ is trivial. The equality is one of subgroups, not merely of their underlying sets.
--
--   This identifies the first step of the principal-unit filtration $U^{(k)} = 1 + \mathfrak{m}^k$ of $R^\times$ with the kernel of reduction to the residue field, so that $R^\times/U^{(1)} \cong (R/\mathfrak{m})^\times$. It serves as the bridge between the project's filtration and Mathlib's reduction homomorphism on units, and is used in computing the index of $U^{(1)}$ in $R^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_principalUnits_one_eq_ker_map_residue.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsLocalRing.principalUnits_one_eq_ker_map_residue {R : Type*} [CommRing R] [IsLocalRing R] :
    principalUnits R 1 = (Units.map (residue R : R →* ResidueField R)).ker := by sorry
