-- Prove2me | Theorems.Thm_Ideal_exists_mem_forall_not_mem_of_forall_not_le
-- name    : Ideal.exists_mem_forall_not_mem_of_forall_not_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/e8677757-97e3-5059-bf74-895fa40eddf4
-- title:
--   Prime avoidance in pointwise form
-- statement:
--   Let $R$ be a commutative ring, let $J$ be an ideal of $R$, and let $S$ be a finite set of ideals of $R$. Assume that every $P \in S$ is prime, and that no $P \in S$ contains $J$, i.e. $J \not\le P$ for all $P \in S$. Then there is a single element $i$ of $J$ with $i \notin P$ for every $P \in S$. Note that the membership conditions are relative to the finite set $S$, so when $S$ is empty the conclusion is satisfied by any element of $J$; the hypotheses $hS$ and $h$ are quantified over the members of $S$ only, and no assumption is made on the ideals of $R$ outside $S$, nor on $J$ beyond its not being contained in any member of $S$. The conclusion is the pointwise strengthening of the assertion that $J$ is not contained in the union $\bigcup_{P \in S} P$: one element of $J$ works simultaneously for all the primes listed in $S$.
--
--   This is prime avoidance, stated contrapositively: an ideal contained in no one of finitely many primes has an element outside all of them. It is used in the construction of a ring element that is simultaneously prescribed on a finite family of conjugate valuation subrings, in [`Subring.exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring`](thm.html#Subring.exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_mem_forall_not_mem_of_forall_not_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.exists_mem_forall_not_mem_of_forall_not_le
    {R : Type*} [CommRing R] (J : Ideal R) (S : Finset (Ideal R))
    (hS : ∀ P ∈ S, P.IsPrime) (h : ∀ P ∈ S, ¬ J ≤ P) :
    ∃ i ∈ J, ∀ P ∈ S, i ∉ P := by sorry
