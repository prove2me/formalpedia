-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_isSq_iff_even_factorization
-- name    : OddPerfectNumber.Kernel.isSq_iff_even_factorization
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T06:47:26.896223+00:00
-- url     : https://prove2.me/theorems/28b00e2d-2e78-4683-8075-7135bec4a50b
-- title:
--   A positive natural number is a square exactly when all its prime exponents are even
-- statement:
--   For a nonzero natural number $n$, $n$ is a perfect square if and only if the exponent of every prime in $n$ is even. This is the bridge between the $\exists y, y^2 = n$ predicate used in the Dris index statements and the prime exponents $\mathrm{factorization}\, n\, p$ used to analyse them. The forward direction is $\mathrm{factorization\_pow}$ applied to $y^2$; the reverse reconstructs the square as the product of $p^{e_p/2}$ over the prime support and identifies it with $n$ by uniqueness of the factorization function.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (factorization_pow at line 182, eq_of_factorization_eq at line 105) and Mathlib/Data/Nat/PrimeFin.lean (primeFactors at line 37). Elementary exponent-parity bookkeeping; it encodes no conjecture-specific content.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem isSq_iff_even_factorization {n : Nat} (hn : n ≠ 0) :
    (∃ y, y ^ 2 = n) ↔ ∀ p : Nat, Even (n.factorization p) := by
  sorry

end OddPerfectNumber.Kernel
