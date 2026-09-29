-- Prove2me | Theorems.Thm_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime
-- name    : Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/8b75fd44-0e11-53cb-8c47-7c7d2462688a
-- title:
--   A prime with DVR localisation has height one
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, and let $p$ be a prime ideal of $R$. The hypothesis is that the localisation $R_p$ of $R$ at $p$, realised as `Localization.AtPrime p`, is a discrete valuation ring in the sense of Mathlib's `IsDiscreteValuationRing`. The conclusion is that the height of $p$, namely `Ideal.height p`, the supremum of the lengths of chains of prime ideals descending from $p$, taken as an element of $\mathbb{N}\infty$, equals $1$. No Noetherian hypothesis and no normality hypothesis is imposed on $R$ itself; the entire input is that the local ring at $p$ is a discrete valuation ring. In particular the conclusion is an equality of extended natural numbers, so it asserts both that $p$ is not a minimal prime (here, not $(0)$) and that every chain of primes below $p$ has length at most one.
--
--   This is the elementary half of the height-one dictionary: a prime localises to a discrete valuation ring only if it has height one, the converse direction to the Serre $R_1$-type criterion which produces a discrete valuation ring from a height-one prime of a Noetherian normal domain. It is used to obtain height one for primes associated to a module over an integrally closed domain, in [`IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes`](thm.html#IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime
    {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime p)) : p.height = 1 := by sorry
