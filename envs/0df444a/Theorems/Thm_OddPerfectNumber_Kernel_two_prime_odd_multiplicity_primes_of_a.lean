-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_odd_multiplicity_primes_of_a
-- name    : OddPerfectNumber.Kernel.two_prime_odd_multiplicity_primes_of_a
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T16:37:26.881961+00:00
-- url     : https://prove2.me/theorems/89d076b4-d7b5-4a1d-a263-55ad181d1569
-- title:
--   A square q*r*a*b with gcd a b = 1 forces the odd-multiplicity primes of a into {q, r}
-- statement:
--   Let $a$ and $b$ be coprime nonzero natural numbers, and let $q$ and $r$ be distinct primes. If $q \cdot r \cdot a \cdot b$ is a perfect square, then every prime occurring to an odd multiplicity in $a$, or in $b$, must be $q$ or $r$. This is the correct parity statement for a two-prime square-free kernel. The stronger claim that $a$ equals $q$ times a square and $b$ equals $r$ times a square is false in general, because $a$ alone may carry two odd-multiplicity primes: $a = 15$ and $b = 77$ are coprime non-squares whose square-free parts each involve two primes. The proof uses the exponent-parity characterisation of squares, the multiplicativity of $\mathrm{factorization}$ over products, and the fact that a prime dividing both $a$ and $b$ would divide their gcd, which is $1$. This is elementary bookkeeping and encodes no conjecture-specific content.
-- source:
--   Odd Perfect Number Conjecture, $k=5$ branch: reducing the square-free part of the Dris index to exactly two primes $q<r$ turns the first Dris equation into $m^2 = d_1^2 q r U V$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$. The square-free structure of $U$ and $V$ then has to be read off from exponent parity. This child records the parity statement that is actually valid, namely that the witness primes are confined to the two kernel primes $q$ and $r$; it deliberately does not assert the false one-prime-per-factor source split. Elementary bookkeeping from the exponent characterisation of squares.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_odd_multiplicity_primes_of_a {a b q r : Nat} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : Nat.gcd a b = 1) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hsq : ∃ y, y ^ 2 = q * r * a * b) (t : Nat) (ht : t.Prime) (htd : t ∣ a)
    (ht0 : ¬ Even (a.factorization t)) : t = q ∨ t = r := by
  sorry

end OddPerfectNumber.Kernel
