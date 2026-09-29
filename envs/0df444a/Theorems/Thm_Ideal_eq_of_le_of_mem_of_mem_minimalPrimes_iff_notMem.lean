-- Prove2me | Theorems.Thm_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem
-- name    : Ideal.eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/b59130ce-4587-5b6c-9514-51ad7c62e1af
-- title:
--   Minimal iff avoiding π below Q forces Q' = Q
-- statement:
--   Let $B$ be a commutative Noetherian ring, let $\pi \in B$, and let $Q, Q'$ be prime ideals of $B$ with $Q' \subseteq Q$ and $\pi \in Q'$. Assume further that for every prime ideal $\mathfrak p$ of $B$ with $\mathfrak p \subseteq Q$ one has the equivalence: $\mathfrak p$ belongs to `minimalPrimes B`, i.e. $\mathfrak p$ is a minimal element of the set of prime ideals of $B$, if and only if $\pi \notin \mathfrak p$. The conclusion is that $Q' = Q$. Thus, under the assumption that below $Q$ minimality among primes is equivalent to avoiding $\pi$, no prime containing $\pi$ lies strictly below $Q$: $Q$ is the unique prime contained in $Q$ that contains $\pi$ and is contained in any prescribed such prime, so that $Q$ is an isolated point of $V(\pi) \cap \operatorname{Spec} B_Q$.
--
--   A localisation-theoretic isolatedness statement proved from Krull's principal ideal theorem together with prime avoidance: it says that if, below $Q$, the generic (minimal) primes are exactly those avoiding $\pi$, then $V(\pi)$ has no point strictly below $Q$. It is used in the proof of [`Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber`](thm.html#Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber), where quasi-finiteness on a generic fibre is propagated under flatness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem
    {B : Type*} [CommRing B] [IsNoetherianRing B] {π : B} {Q Q' : Ideal B}
    [Q.IsPrime] [Q'.IsPrime] (hle : Q' ≤ Q) (hπ : π ∈ Q')
    (h : ∀ p : Ideal B, p.IsPrime → p ≤ Q → (p ∈ minimalPrimes B ↔ π ∉ p)) : Q' = Q := by sorry
