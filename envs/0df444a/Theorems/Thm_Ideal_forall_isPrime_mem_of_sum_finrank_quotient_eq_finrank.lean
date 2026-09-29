-- Prove2me | Theorems.Thm_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
-- name    : Ideal.forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/94509f3e-2ca3-5c39-a91a-0461f238a5ec
-- title:
--   Primes exhaust S when residue degrees sum to dim_F R
-- statement:
--   Let $F$ be a field and $R$ a commutative ring that is an $F$-algebra, finite as an $F$-module, and reduced. Let $S$ be a finite set of ideals of $R$ such that every $\mathfrak p \in S$ is prime, and suppose that the residue degrees over $S$ add up to the total rank, $$\sum_{\mathfrak p \in S} \dim_F (R/\mathfrak p) = \dim_F R,$$ where $\dim_F$ denotes `Module.finrank` over $F$ (so each $R/\mathfrak p$ is regarded as an $F$-module via the quotient map). The conclusion is that $S$ already contains every prime ideal of $R$: for all $\mathfrak p :$ `Ideal R`, if $\mathfrak p$ is prime then $\mathfrak p \in S$. Note that the sum is taken over the finite set $S$ of ideals, and primality of its members is a hypothesis rather than part of the type; no ordering or maximality of the members is assumed, and no distinctness condition beyond that implicit in $S$ being a `Finset`.
--
--   An exhaustion, or component-counting, lemma for finite algebras over a field: once a finite family of primes accounts for the whole $F$-dimension of $R$, no further prime can exist. It is used by [`Ideal.forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq`](thm.html#Ideal.forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq), where a family of primes produced by a degree computation is shown to consist of all the primes of the algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
    (S : Finset (Ideal R)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsPrime)
    (hsum : ∑ 𝔭 ∈ S, Module.finrank F (R ⧸ 𝔭) = Module.finrank F R) :
    ∀ 𝔭 : Ideal R, 𝔭.IsPrime → 𝔭 ∈ S := by sorry
