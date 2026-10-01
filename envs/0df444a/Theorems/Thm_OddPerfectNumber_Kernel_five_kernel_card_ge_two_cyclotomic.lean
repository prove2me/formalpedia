-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_kernel_card_ge_two_cyclotomic
-- name    : OddPerfectNumber.Kernel.five_kernel_card_ge_two_cyclotomic
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T13:03:34.437062+00:00
-- url     : https://prove2.me/theorems/36a295ec-1b7d-4d8f-b96b-062970c05338
-- title:
--   In the $k = 5$ Dris branch the square-free part of the index has at least two prime factors
-- statement:
--   Let $p \ge 5$ be a prime with $p \equiv 1 \pmod 4$, let $m$ be odd with $p \nmid m$, and suppose $\sigma(p^5)\, s = 2 m^2$ where $\sigma$ is the sum of divisors and $s$ is not a perfect square. Write $s = d_1^2 d_2$ with $d_2$ square-free. Then $d_2$ has at least two distinct prime factors, i.e. $\omega(d_2) \ge 2$.
--
--   The hypothesis is written with $\sigma(p^5)$ already replaced by its proved factorisation $2(p^2+p+1)\left(\frac{p+1}{2}\right)(p^2-p+1)$ from `OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd_prime` (7f2041ff-30b4-4c8d-ad98-798dc15b91e1). That substitution is exactly equivalent to the first Dris equation $2m^2 = \sigma(p^5) s$, but it keeps the binder free of a summation, which is what the target needs both to state the hypothesis and to feed it to the one-prime-kernel exclusion.
--
--   The proof is a direct assembly of three already-proved `Kernel` children. First, $d_2 \neq 1$, because otherwise $s = d_1^2$ contradicts the non-square hypothesis; this is `OddPerfectNumber.Kernel.sqfree_part_ne_one` (b59073fb-8d9c-4e9a-b160-acdd1be9cc25). Second, $d_2$ cannot be prime: if $d_2 = q$ for a prime $q$ then $s = d_1^2 q$ is a prime times a square, which `OddPerfectNumber.Kernel.five_index_not_prime_mul_square` (2ec27119-2f77-425b-ab15-a95e11c2f9bc) excludes using only the first Dris equation. Third, `OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime` (9c90129e-60c2-4fa1-aa32-c55ece1e485d) turns the two exclusions into the cardinality bound.
--
--   This statement replaces `OddPerfectNumber.Kernel.five_kernel_card_ge_two` (5ef998ce-3d09-4f41-8acc-0a6c651ef59f), which omitted the Dris equation and is false as stated: taking $s = 7$, $d_1 = 1$, $d_2 = 7$ satisfies every one of its hypotheses while its conclusion $2 \le 1$ fails.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_kernel_card_ge_two_cyclotomic (p m s d1 d2 : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_nsq : ¬ ∃ r, s = r ^ 2)
    (hd2 : d1 ^ 2 * d2 = s) (hd2pos : 0 < d2) (hdsf : Squarefree d2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * s) :
    2 ≤ d2.primeFactors.card := by
  sorry

end OddPerfectNumber.Kernel
