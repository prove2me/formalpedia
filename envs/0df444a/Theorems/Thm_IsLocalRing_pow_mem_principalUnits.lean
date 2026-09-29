-- Prove2me | Theorems.Thm_IsLocalRing_pow_mem_principalUnits
-- name    : IsLocalRing.pow_mem_principalUnits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/a658ef41-1911-55a8-9aa3-ec68536d268f
-- title:
--   Wild step of the principal unit filtration
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m =$ `maximalIdeal R`, and for $k \in \mathbb N$ let `principalUnits R k` denote the subgroup of $R^\times$ consisting of those units $u$ with $(u : R) - 1 \in \mathfrak m^k$. Let $p$ be a prime number and $e \in \mathbb N$ be such that the image of $p$ in $R$ lies in $\mathfrak m^e$. Then for every $k \in \mathbb N$ and every unit $u \in R^\times$ with $(u : R) - 1 \in \mathfrak m^k$, the $p$-th power $u^p$ satisfies $(u^p : R) - 1 \in \mathfrak m^{\min(pk,\, k+e)}$, i.e. $u^p \in$ `principalUnits R (min (p * k) (k + e))`. No discreteness, Noetherian, completeness or regularity hypothesis on $R$ is imposed, and $k$ and $e$ are arbitrary natural numbers.
--
--   This is the wild (p-power) step of the filtration of the unit group of a local ring by principal units: raising to the $p$-th power moves the filtration index from $k$ to $\min(pk, k+e)$, where $e$ measures the divisibility of $p$ in $\mathfrak m$. It is used in the study of the $p$-power map on principal units of a discrete valuation ring, being cited by [`IsDiscreteValuationRing.map_powMonoidHom_principalUnits`](thm.html#IsDiscreteValuationRing.map_powMonoidHom_principalUnits).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_pow_mem_principalUnits.lean

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing

theorem IsLocalRing.pow_mem_principalUnits {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : (p : R) ∈ maximalIdeal R ^ e)
    {k : ℕ} {u : Rˣ} (hu : u ∈ principalUnits R k) :
    u ^ p ∈ principalUnits R (min (p * k) (k + e)) := by sorry
