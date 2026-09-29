-- Prove2me | Theorems.Thm_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime
-- name    : IsLocalRing.isUnit_natCast_or_isUnit_natCast_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/2ff82a03-425b-587a-93e7-7f96a4678712
-- title:
--   Coprime naturals: one is a unit in a local ring
-- statement:
--   Let $R$ be a commutative ring which is local (in Mathlib's sense: a ring with a unique maximal ideal, equivalently in which the non-units form an ideal), and let $m, n$ be natural numbers whose greatest common divisor is $1$, i.e. `Nat.Coprime m n`. The assertion is the disjunction: either the image of $m$ under the canonical map $\mathbb{N} \to R$ is a unit of $R$, or the image of $n$ is a unit of $R$. No claim is made about which of the two alternatives holds, and both may hold simultaneously (for instance when $R$ has residue characteristic $0$ or a prime dividing neither $m$ nor $n$). Equivalently, at least one of $m$, $n$ has non-zero image in the residue field of $R$; when that residue field has characteristic $p > 0$, at least one of $m$, $n$ is prime to $p$.
--
--   An elementary selection principle for local rings: of two coprime integers, at least one avoids the residue characteristic. It serves as the "choose the auxiliary prime" step in situations where two distinct primes are available, and is used here in the construction of an indefinite rational quaternion algebra ramified exactly at a prescribed set, where at a given place one of the two ramified primes must be invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.isUnit_natCast_or_isUnit_natCast_of_coprime
    {R : Type*} [CommRing R] [IsLocalRing R] {m n : ℕ} (h : Nat.Coprime m n) :
    IsUnit (m : R) ∨ IsUnit (n : R) := by sorry
