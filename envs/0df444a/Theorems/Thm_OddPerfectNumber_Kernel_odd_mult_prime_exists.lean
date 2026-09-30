-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_odd_mult_prime_exists
-- name    : OddPerfectNumber.Kernel.odd_mult_prime_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T20:17:06.403434+00:00
-- url     : https://prove2.me/theorems/ffeb6765-ce67-43db-a9b6-5073e23eccdf
-- title:
--   A non-square natural number has a prime factor of odd multiplicity
-- statement:
--   If $a$ is a nonzero natural number that is not a perfect square then some prime $t$ divides $a$ to an odd multiplicity, i.e. $a.factorization\, t$ is not even. Mathlib has no $\mathbb{N}$-valued square predicate, so squares are phrased with $\exists y,\, y^2 = a$ to match the surrounding $k=5$ children. The proof uses the accepted bridge OddPerfectNumber.Kernel.isSq_iff_even_factorization (28b00e2d-2e78-4683-8075-7135bec4a50b), which characterises squares by even prime multiplicities: if every multiplicity were even then $a$ would be a square, so some $t$ has odd multiplicity; that multiplicity value is nonzero, so $t$ lies in the support of $a$, which makes $t$ a prime dividing $a$. This is the forcing half of the contextual two-prime argument and is elementary exponent bookkeeping; it encodes no conjecture-specific content.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (support_factorization, mem_primeFactors, prime_of_mem_primeFactors) and Mathlib/Data/Nat/Factorization/Basic.lean (dvd_of_factorization_pos), together with the accepted bridge OddPerfectNumber.Kernel.isSq_iff_even_factorization (28b00e2d-2e78-4683-8075-7135bec4a50b). Elementary exponent-parity bookkeeping; it encodes no conjecture-specific content.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem odd_mult_prime_exists {a : Nat} (ha0 : a ≠ 0) (hna : ¬ ∃ y, y ^ 2 = a) :
    ∃ t : Nat, t.Prime ∧ t ∣ a ∧ ¬ Even (a.factorization t) := by
  sorry

end OddPerfectNumber.Kernel
