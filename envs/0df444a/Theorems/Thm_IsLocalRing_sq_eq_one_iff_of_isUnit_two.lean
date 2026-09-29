-- Prove2me | Theorems.Thm_IsLocalRing_sq_eq_one_iff_of_isUnit_two
-- name    : IsLocalRing.sq_eq_one_iff_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/8812c185-0c83-5b1a-a63c-a482a03331b1
-- title:
--   Square roots of unity in a local ring with 2 invertible
-- statement:
--   Let $R$ be a commutative ring that is local (in the sense of Mathlib's `IsLocalRing`: the nonunits form an ideal, equivalently the sum of two nonunits is a nonunit, together with nontriviality), suppose the element $2$ of $R$ is a unit, and let $u \in R$. The theorem asserts the equivalence $u^2 = 1 \iff u = 1$ or $u = -1$. Thus $1$ and $-1$ are the only square roots of $1$ in such a ring; no reduction or finiteness hypothesis is imposed, and $R$ need not be reduced or a domain. The statement is an iff, so the converse direction — that $u = 1$ or $u = -1$ forces $u^2 = 1$ — is included.
--
--   An elementary fact about units in local rings: the group of square roots of $1$ is $\{\pm 1\}$ once $2$ is invertible. It is used to show that an involutive Hecke operator acting on a module over a local Hecke algebra of odd residue characteristic acts by the scalar $+1$ or $-1$, in the analysis of the corner submodule at a place where the relevant representation is not unramified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_sq_eq_one_iff_of_isUnit_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.sq_eq_one_iff_of_isUnit_two {R : Type} [CommRing R] [IsLocalRing R]
    (h2 : IsUnit (2 : R)) (u : R) : u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by sorry
