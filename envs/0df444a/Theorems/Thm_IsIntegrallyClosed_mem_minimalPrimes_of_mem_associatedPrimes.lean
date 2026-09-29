-- Prove2me | Theorems.Thm_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes
-- name    : IsIntegrallyClosed.mem_minimalPrimes_of_mem_associatedPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/80d3b80c-cbed-51f7-9c2c-ccdb28549d37
-- title:
--   Associated primes of A/(x) are minimal over (x)
-- statement:
--   Let $A$ be a commutative ring which is a Noetherian integral domain and integrally closed in its fraction field, let $x \in A$ be a non-zero element, and let $P$ be an ideal of $A$ which is prime. Assume $P$ lies in $\operatorname{Ass}_A(A/(x))$, the set of associated primes of the $A$-module $A / \operatorname{span}\{x\}$, i.e. $P$ is prime and is the annihilator of some element of $A/(x)$. The conclusion is that $P$ belongs to $(\operatorname{span}\{x\})^{\mathrm{minimalPrimes}}$: $P$ is a prime ideal containing $\operatorname{span}\{x\}$ and is minimal with this property, that is, whenever a prime ideal $q$ satisfies $\operatorname{span}\{x\} \le q \le P$ one has $q = P$. Thus $A/(x)$ has no embedded primes: every associated prime of a non-zero principal quotient of a Noetherian normal domain is a minimal prime over $(x)$.
--
--   This is the elementary form of Serre's condition $S_2$ for a normal Noetherian domain, applied to the quotient by a non-zero principal ideal, and is the statement that a principal hypersurface in a normal domain has no embedded primes. It is used in the project to reduce questions about the quotient $A/(x)$ — reducedness of such a quotient, and the recovery of a principal ideal from its minimal primes — to the finitely many generic points of $\operatorname{Spec} A/(x)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsIntegrallyClosed.mem_minimalPrimes_of_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ associatedPrimes A (A ⧸ Ideal.span {x})) :
    P ∈ (Ideal.span {x}).minimalPrimes := by sorry
