-- Prove2me | Theorems.Thm_IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem
-- name    : IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/7984b7af-d03b-5476-89c4-2392bb1d93d4
-- title:
--   Element of 𝔪∖𝔪² avoiding all minimal primes
-- statement:
--   Let $R$ be a commutative ring which is local (so has a unique maximal ideal $\mathfrak m =$ `maximalIdeal R`) and Noetherian, and assume its Krull dimension `ringKrullDim R`, taken as an element of the extended integers, is strictly positive. The assertion is the existence of an element $x$ of $\mathfrak m$ with two further properties: first, $x \notin \mathfrak m^2$; second, for every prime ideal $\mathfrak p$ belonging to `minimalPrimes R`, that is, every minimal element of the set of prime ideals of $R$ (equivalently, every minimal prime over the zero ideal), one has $x \notin \mathfrak p$. Thus $x$ lies in $\mathfrak m$ but in none of the ideals $\mathfrak m^2$ and $\mathfrak p$, $\mathfrak p \in \operatorname{Min}(R)$. No claim is made that $x$ is a non-zero-divisor, nor that $x$ is part of a regular system of parameters.
--
--   This is the standard prime-avoidance selection step: in a Noetherian local ring of positive dimension the maximal ideal is not contained in $\mathfrak m^2$ (Nakayama) nor in any minimal prime, and there are only finitely many minimal primes, so an element avoiding all of them at once exists. It is used in the inductive proof that regular local rings of small dimension are unique factorisation domains, via [`IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two`](thm.html#IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by sorry
