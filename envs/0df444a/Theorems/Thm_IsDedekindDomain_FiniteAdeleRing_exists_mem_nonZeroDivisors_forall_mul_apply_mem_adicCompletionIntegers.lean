-- Prove2me | Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
-- name    : IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/509b4dca-d2f4-5d86-a8dd-b5bbe7287a70
-- title:
--   Common denominator for a finite adele
-- statement:
--   Let $A$ be a Dedekind domain with a field $K$ equipped with an $A$-algebra structure making it the fraction field of $A$, and let $a$ be an element of the finite adele ring $\mathbb{A}_{A,K}^{f}$, i.e. the restricted product of the completions $K_v$ with respect to the valuation rings $\mathcal{O}_v$, taken over $v$ in the height-one spectrum of $A$ (the nonzero primes). The assertion is that there exists $d$ in the monoid of non-zero-divisors of $A$ such that for every height-one prime $v$ of $A$, the image of $d$ in $K_v$ under the composite $A \to K \to K_v$, multiplied by the $v$-component $a_v$ of $a$, lies in $\mathcal{O}_v =$ `v.adicCompletionIntegers K`. In other words, a single denominator $d$, a non-zero-divisor of $A$ (equivalently, a nonzero element, since $A$ is a domain), clears the denominators of all components of $a$ simultaneously. Note that the scalar is written explicitly as `algebraMap K (v.adicCompletion K) (algebraMap A K d)` rather than as a single algebra map from $A$.
--
--   This is the standard statement that every finite adele has a common denominator in the base ring, the integral-scaling step underlying strong approximation at the finite places. It is used in the treatment of orders in quaternion algebras, for conjugation of an order by a finite idele and the associated unit criterion, and in producing nonzero integer multiples landing in an adelic box.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain

theorem IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      algebraMap K (v.adicCompletion K) (algebraMap A K d) * a v ∈ v.adicCompletionIntegers K := by sorry
