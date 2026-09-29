-- Prove2me | Theorems.Thm_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
-- name    : IsRegularLocalRing.isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/f100e223-1465-5a9e-a93c-48fa0c6651f8
-- title:
--   Localisation at a regular parameter is a DVR
-- statement:
--   Let $R$ be a commutative ring that is an integral domain, is a regular local ring, and satisfies `IsRegularRing`, and let $x \in R$ satisfy $x \in \mathfrak m$, $x \notin \mathfrak m^{2}$ and $x \neq 0$, where $\mathfrak m =$ `maximalIdeal R` is the maximal ideal of $R$. The conclusion asserts the existence of a witness $hP$ for the statement that the principal ideal $\mathrm{span}\{x\}$ is prime, such that two further assertions hold for it: the height of $\mathrm{span}\{x\}$, in the sense of `Ideal.height`, equals $1$; and the localisation of $R$ at the prime $\mathrm{span}\{x\}$, formed using that witness as the primality instance, is a discrete valuation ring. The existential over the proof $hP$ is what allows the localisation at a prime, whose formation needs primality as an instance argument, to be named in the same statement. Nothing is asserted here about the residue field of that localisation.
--
--   This is the standard fact that a regular parameter of a regular local domain generates a height-one prime whose associated localisation is a discrete valuation ring, the local source of the discrete valuations used on regular two-dimensional bases. It is used by [`IsRegularLocalRing.quotient_span_singleton_isAdicComplete_of_notMem_sq`](thm.html#IsRegularLocalRing.quotient_span_singleton_isAdicComplete_of_notMem_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
    (R : Type) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [IsRegularRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) (hx0 : x ≠ 0) :
    ∃ hP : (Ideal.span {x}).IsPrime, (Ideal.span {x}).height = 1 ∧
      @IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {x}) (hp := hP)) _ _ := by sorry
