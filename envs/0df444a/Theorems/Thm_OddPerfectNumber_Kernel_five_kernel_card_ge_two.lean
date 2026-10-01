-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_kernel_card_ge_two
-- name    : OddPerfectNumber.Kernel.five_kernel_card_ge_two
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T12:12:34.255603+00:00
-- url     : https://prove2.me/theorems/5ef998ce-3d09-4f41-8acc-0a6c651ef59f
-- title:
--   The square-free part of the k=5 Dris index has at least two distinct prime factors
-- statement:
--   Let $N = n^2 q^k$ be an odd perfect number with $k = 5$, and let $s$ be its Dris index, so $2m^2 = \sigma(p^5)\, s$ for the Euler prime $p$ and the cofactor $m$. Suppose the square-free part of $s$ is written as $s = d_1^2 d_2$ with $d_2$ square-free and $s$ is not itself a square. Then the square-free part has at least two distinct prime factors: $\#\mathrm{primeFactors}(d_2) \ge 2$.
--
--   The argument is short once the two exclusions are in place. If $d_2 = 1$ then $s = d_1^2$ is a square, contradicting the hypothesis; that is the accepted child OddPerfectNumber.Kernel.sqfree_part_ne_one (b59073fb). If $d_2$ is a prime $q$ then $s = d_1^2 \cdot q$ is exactly a prime times a square, which the accepted child OddPerfectNumber.Kernel.five_index_not_prime_mul_square (2ec27119) forbids, since it uses only the first Dris equation together with the factorisation $\sigma(p^5) = 2(p^2+p+1)\frac{p+1}{2}(p^2-p+1)$ and the coprimality and non-square properties of the two cyclotomic blocks. The accepted generic lemma OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime (9c90129e) then converts the two exclusions into the bound of two.
--
--   This is the $\ge 2$ half of the target $\omega(\mathrm{squarefree\_part}(s)) \ge 3$ for the $k=5$ Dris branch of OddPerfectNumber.no_dris_five_s_odd_ge_five_nonsq. The remaining half is the genuine research residual: excluding $d_2 = q r$ for two distinct primes, which the two-prime case genuinely satisfies as far as the first Dris equation alone is concerned (at $p = 5$, $s = 217 = 7\cdot 31$, $m = 651$ one has exactly $2\cdot 651^2 = 3906 \cdot 217$), so the second Dris equation $\sigma(m^2) = p^5 s$ is indispensable there.
-- source:
--   Mathlib only, composed from three accepted Prove2Me children of this mission: OddPerfectNumber.Kernel.sqfree_part_ne_one (b59073fb-8d9c-4e9a-b160-acdd1be9cc25), OddPerfectNumber.Kernel.five_index_not_prime_mul_square (2ec27119-2f77-425b-ab15-a95e11c2f9bc) and OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime (9c90129e-60c2-4fa1-aa32-c55ece1e485d). The last of these is pure Mathlib finite-set and factorization bookkeeping, matching the idiom of the accepted sibling OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small (64627c09). No coprimality between $d_1$ and $d_2$ is required: for a square-free $d_2$ that is prime, $d_1^2 d_2 = q (d_1)^2$ is already of the forbidden shape prime times a square, and reassociating the product is all that is needed. The $k=5$ content lives entirely in the accepted exclusion, whose proof uses the factorisation $\sigma(p^5) = 2 (p^2+p+1) \left(\frac{p+1}{2}\right)(p^2-p+1)$, the coprimality of the two blocks, and their individual non-square properties under $p \equiv 1 \pmod 4$.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_kernel_card_ge_two (p m s d1 d2 : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_nsq : ¬ ∃ r : Nat, s = r ^ 2)
    (hd2 : d1 ^ 2 * d2 = s) (hd2pos : 0 < d2) (hdsf : Squarefree d2) :
    2 ≤ d2.primeFactors.card := by
  sorry

end OddPerfectNumber.Kernel
