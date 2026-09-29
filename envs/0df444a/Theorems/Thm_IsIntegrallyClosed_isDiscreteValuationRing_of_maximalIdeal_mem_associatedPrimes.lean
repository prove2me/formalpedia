-- Prove2me | Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
-- name    : IsIntegrallyClosed.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/46f48cb2-9972-5dca-8046-d7a56f41c545
-- title:
--   Normal Noetherian local domain with depth one is a DVR
-- statement:
--   Let $B$ be a commutative ring which is an integral domain, Noetherian, integrally closed in its field of fractions, and local, with maximal ideal $\mathfrak n =$ `IsLocalRing.maximalIdeal B`. Let $x \in B$ be nonzero, and assume that $\mathfrak n$ is an associated prime of the $B$-module $B/xB$, that is, $\mathfrak n$ belongs to `associatedPrimes B (B ⧸ Ideal.span {x})`: $\mathfrak n$ is prime and is the annihilator of some element of $B/xB$. The conclusion is that $B$ is a discrete valuation ring in Mathlib's sense, namely a local principal ideal domain which is not a field. Thus the only input beyond the standing hypotheses on $B$ is the existence of one nonzero $x$ for which the maximal ideal occurs among the associated primes of $B/xB$; equivalently, in classical language, that $B$ has depth one.
--
--   This is the standard characterisation, going back to Krull and appearing as a step in Serre's normality criterion, of a one-dimensional normal Noetherian local domain as a discrete valuation ring, here formulated with the depth hypothesis in the form '$\mathfrak n$ is an associated prime of $B/xB$'. It is used by [`IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes`](thm.html#IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes), which transfers the conclusion to localisations of a normal Noetherian domain at such associated primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegrallyClosed.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [IsLocalRing B]
    {x : B} (hx : x ≠ 0)
    (h : IsLocalRing.maximalIdeal B ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing B := by sorry
