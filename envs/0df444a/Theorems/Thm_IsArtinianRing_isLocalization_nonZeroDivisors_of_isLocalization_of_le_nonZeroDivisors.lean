-- Prove2me | Theorems.Thm_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors
-- name    : IsArtinianRing.isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/eba2e47f-5060-5f26-974e-a5e76fbb6502
-- title:
--   Artinian localisation at non-zero-divisors is the total quotient ring
-- statement:
--   Let $B$ and $F$ be commutative rings with $F$ a $B$-algebra, and let $M$ be a submonoid of $B$ contained in the submonoid $\mathrm{nonZeroDivisors}\,B$ of non-zero-divisors of $B$. Assume, as typeclass hypotheses, that the structure map $B \to F$ exhibits $F$ as the localisation of $B$ at $M$, and that $F$ is an Artinian ring. The conclusion is that the same structure map exhibits $F$ as the localisation of $B$ at the whole submonoid of non-zero-divisors of $B$; that is, $F$ satisfies the defining properties of $\mathrm{IsLocalization}(\mathrm{nonZeroDivisors}\,B, F)$: every non-zero-divisor of $B$ maps to a unit of $F$, every element of $F$ is of the form $b/s$ with $b \in B$ and $s$ a non-zero-divisor, and two elements of $B$ have the same image exactly when they are identified after multiplication by some non-zero-divisor. Since $M$ consists of non-zero-divisors, this says in classical language that $F$ is the total quotient ring of $B$.
--
--   This is the standard fact that a localisation of $B$ at a multiplicative set of non-zero-divisors which happens to be Artinian is already the total ring of fractions of $B$; it is used when a module-finite algebra's generic fibre, being finite-dimensional over a field and hence Artinian, is identified with $Q(B)$, and in particular with $\mathrm{Frac}(B)$ once $B$ is a domain. It is invoked in the proof of [`IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing`](thm.html#IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsArtinianRing.isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors
    {B F : Type*} [CommRing B] [CommRing F] [Algebra B F]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M F] [IsArtinianRing F] :
    IsLocalization (nonZeroDivisors B) F := by sorry
