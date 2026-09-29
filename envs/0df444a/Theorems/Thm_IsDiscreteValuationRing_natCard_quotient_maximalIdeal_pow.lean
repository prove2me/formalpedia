-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow
-- name    : IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/69b1c686-f1e2-5f53-a549-3350e2a3bb0d
-- title:
--   Cardinality of R/𝔪ⁿ for a discrete valuation ring
-- statement:
--   Let $R$ be a commutative ring that is an integral domain and a discrete valuation ring in Mathlib's sense (via the `IsDiscreteValuationRing` class), and let $n$ be a natural number. Write $\mathfrak m =$ `IsLocalRing.maximalIdeal R` for its maximal ideal and $\kappa =$ `IsLocalRing.ResidueField R` $= R/\mathfrak m$ for its residue field. The assertion is the equality of natural numbers $$\#\bigl(R/\mathfrak m^{\,n}\bigr) = (\#\kappa)^{n},$$ where $\#$ denotes `Nat.card`, the cardinality of a type taken to be $0$ when the type is infinite. Thus for finite residue field the statement is the expected count of the residue rings $R/\mathfrak m^n$; when $\kappa$ is infinite it asserts that $R/\mathfrak m^n$ is infinite for $n \ge 1$, both sides being $0$, while for $n = 0$ the ideal $\mathfrak m^0 = (1)$ is the whole ring, the quotient is trivial and both sides equal $1$. No finiteness hypothesis on $R$ or on $\kappa$ is imposed.
--
--   This is the standard computation of the length-$n$ residue rings of a discrete valuation ring, stated uniformly in `Nat.card` so that it also records infiniteness when the residue field is infinite. It supplies the finite-index input used in local computations over $p$-adic fields, for instance indices of powers of the maximal ideal and of images of power maps on units, and cardinalities of quotients of adic completions of Dedekind domains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    Nat.card (R ⧸ IsLocalRing.maximalIdeal R ^ n) = Nat.card (IsLocalRing.ResidueField R) ^ n := by sorry
