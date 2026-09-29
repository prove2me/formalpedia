-- Prove2me | Theorems.Thm_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three
-- name    : NumberField.count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/5dae3aa1-6f5c-53b0-aa3e-1891fa3cc99b
-- title:
--   Different exponent at a prime above 3 is at most e+e v₃(e)-1
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ (the type `NumberField.RingOfIntegers K`), and let $P$ be an ideal of $\mathcal{O}_K$ belonging to `IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (NumberField.RingOfIntegers K)`, that is, to the finite set of primes of $\mathcal{O}_K$ lying over the ideal $3\mathbb{Z}$ of $\mathbb{Z}$. Write $e =$ `(Ideal.span {(3 : ℤ)}).ramificationIdx' P` for the ramification index of $P$ over $3\mathbb{Z}$ in the sense of Mathlib's primed variant. The assertion is that the multiplicity of $P$ as a factor in the multiset `UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (NumberField.RingOfIntegers K))`, i.e. the exponent $v_P(\mathfrak{D}_{K/\mathbb{Q}})$ of $P$ in the different ideal of $\mathcal{O}_K$ over $\mathbb{Z}$, is bounded by
--   $$e + e\cdot v_3(e) - 1,$$
--   where $v_3(e)$ is `padicValNat 3 e`, the exponent of $3$ in $e$, and the subtraction is truncated subtraction of natural numbers. Only the residue characteristic $3$ occurs: the statement is the specialisation to $p = 3$ of the general bound for a prime above $p$.
--
--   This is the classical upper bound for the exponent of a prime in the different of a number field, $v_{\mathfrak{P}}(\mathfrak{D}) \le e - 1 + v_{\mathfrak{P}}(e)$, in the form $e + e\,v_3(e) - 1$ obtained from $v_{\mathfrak{P}}(e) = e\,v_3(e)$, restricted to primes above $3$. It feeds the discriminant estimate [`NumberField.abs_discr_le_three_pow_95_of_isGalois_of_finrank_eq_48`](thm.html#NumberField.abs_discr_le_three_pow_95_of_isGalois_of_finrank_eq_48) for Galois number fields of degree $48$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three
    (K : Type) [Field K] [NumberField K] (P : Ideal (NumberField.RingOfIntegers K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (NumberField.RingOfIntegers K)) :
    (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (NumberField.RingOfIntegers K))).count P
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) - 1 := by sorry
