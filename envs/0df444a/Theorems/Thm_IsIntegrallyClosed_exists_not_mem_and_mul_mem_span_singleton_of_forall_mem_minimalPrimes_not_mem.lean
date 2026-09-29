-- Prove2me | Theorems.Thm_IsIntegrallyClosed_exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem
-- name    : IsIntegrallyClosed.exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/3761f614-4e14-5f82-9fdd-fed1da09a18f
-- title:
--   Unmixedness of principal ideals in normal Noetherian domains, local form
-- statement:
--   Let $A$ be a commutative ring that is a Noetherian integral domain and is integrally closed in its fraction field, let $x \in A$, let $\mathfrak{m} \subseteq A$ be a prime ideal, and let $t \in A$ be an element with the property that for every prime $\mathfrak{q}$ belonging to the minimal primes of the principal ideal $(x)$ and satisfying $\mathfrak{q} \subseteq \mathfrak{m}$, one has $t \notin \mathfrak{q}$. The assertion is then: for every $a \in A$ with $t a \in (x)$, there exists $s \in A$ with $s \notin \mathfrak{m}$ and $s a \in (x)$. In other words, the image of $t$ is a non-zero-divisor on the localisation of $A/xA$ at $\mathfrak{m}$, expressed without localising: an element killed by $t$ modulo $(x)$ is already killed modulo $(x)$ by some element outside $\mathfrak{m}$. No hypothesis $x \neq 0$ is imposed; when $x = 0$ the hypothesis on $t$ amounts to $t \neq 0$, since $(0)$ has the zero ideal as its unique minimal prime.
--
--   This is the local form of the unmixedness of principal ideals in a Noetherian normal domain, i.e. the $(S_2)$ half of Serre's normality criterion packaged as a statement about non-zero-divisors on $A/xA$ localised at a prime. It is used in the proof of [`ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing`](thm.html#ValuationSubring.exists_transcendental_forall_over_gauss_iff_mem_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsIntegrallyClosed.exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (x : A) (𝔪 : Ideal A) [𝔪.IsPrime] (t : A)
    (ht : ∀ 𝔮 ∈ (Ideal.span {x}).minimalPrimes, 𝔮 ≤ 𝔪 → t ∉ 𝔮)
    (a : A) (ha : t * a ∈ Ideal.span {x}) :
    ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {x} := by sorry
