-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_coprime_sq_factor_right
-- name    : OddPerfectNumber.Kernel.coprime_sq_factor_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T17:31:27.888109+00:00
-- url     : https://prove2.me/theorems/da2991de-fbc3-441a-8725-66573ead79bf
-- title:
--   Coprime factors of a square product are each squares
-- statement:
--   If $a$ and $b$ are coprime nonzero natural numbers and their product is a perfect square, then $b$ alone is a perfect square. This is the standard coprime-product lemma. Mathlib has no $\mathbb{N}$-valued square predicate, so the statement is phrased with $\exists y,\, y^2 = _$ to match the surrounding $k=5$ children. The proof uses the accepted bridge OddPerfectNumber.Kernel.isSq_iff_even_factorization, which characterises squares by even prime multiplicities: the multiplicity in $a b$ is the sum of the multiplicities in $a$ and $b$, and coprimality guarantees that at each prime at most one of the two summands is nonzero, so the multiplicity in $b$ is even on its own. This is elementary bookkeeping and encodes no conjecture-specific content.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (Nat.factorization_mul, Nat.factorization_eq_zero_of_not_dvd) and Mathlib/Data/Nat/GCD (dvd_gcd, Coprime.gcd_eq_one), together with the accepted bridge OddPerfectNumber.Kernel.isSq_iff_even_factorization (28b00e2d-2e78-4683-8075-7135bec4a50b). Elementary exponent-parity bookkeeping; it encodes no conjecture-specific content.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem coprime_sq_factor_right {a b : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : a.Coprime b) (hsq : ∃ y, y ^ 2 = a * b) :
    ∃ z, z ^ 2 = b := by
  sorry

end OddPerfectNumber.Kernel
