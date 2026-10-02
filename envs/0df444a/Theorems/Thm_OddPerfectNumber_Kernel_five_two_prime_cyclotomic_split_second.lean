-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_cyclotomic_split_second
-- name    : OddPerfectNumber.Kernel.five_two_prime_cyclotomic_split_second
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T07:27:06.629366+00:00
-- url     : https://prove2.me/theorems/793eb5c3-69c0-425d-b3b1-7f4719cfa0f1
-- title:
--   The second cyclotomic block absorbs one of the two kernel primes
-- statement:
--   This is the mirror of the proved theorem `five_two_prime_cyclotomic_split`, for the second cyclotomic block instead of the first.
--
--   In the $k=5$ Dris branch one writes $N = m^2 q^\alpha$ with $q \equiv 1 \pmod 4$ and $\alpha = 5$, so $\sigma(p^5) = (p+1)(p^2+p+1)(p^2-p+1)$ factors into the two cyclotomic blocks $C = p^2+p+1$ and $D = p^2-p+1$ together with the factor $p+1$.
--
--   Suppose the square-free part of the Dris index $s$ has exactly two distinct prime factors $q < r$, so $s = d_1^2 q r$ for some $d_1$, and suppose the first Dris equation $2 m^2 = \sigma(p^5) s$ holds. Then
--
--   $$m^2 = \frac{(p+1)}{2} \cdot (p^2+p+1) \cdot (p^2-p+1) \cdot d_1^2 \cdot q \cdot r.$$
--
--   Because $m^2$ is a square, every prime must occur to an even multiplicity in the right-hand side. The block $C$ and the block $D$ are coprime, and each is coprime to $(p+1)/2$ except for a single shared factor $3$ between $(p+1)/2$ and $D$. That single overlap is the only place where the two supports can meet, and it can contribute at most one factor of $3$.
--
--   Consequently the odd-multiplicity prime support of $D = p^2-p+1$ is a subset of $\{q, r\}$: any prime dividing $D$ to an odd power must be cancelled by the single occurrence of $q$ or $r$, since every other factor on the right is either a square or coprime to $D$. As $D$ is not a square, that support is non-empty, so $D = q x^2$ or $D = r x^2$ for some $x$.
--
--   **Consequence.** This supplies the missing half of the $3$-adic argument. The proved theorem `five_cyclotomic_primes_one_mod_three` forces both kernel primes to be $1 \pmod 3$, so in particular neither is $3$. For $p \equiv 1 \pmod 3$ the block $C$ carries exactly one factor of $3$ (the proved child `three_val_first_cyclotomic`), while for $p \equiv 2 \pmod 3$ it is the block $D$ that does, with $v_3(D) = 1$ (the child `three_val_second_cyclotomic`). Once this split is available the same Euclid argument that yields $q = 3 \lor r = 3$ from `three_kernel_prime_when_p_one_mod_three` applies to the second block as well, removing every $p \equiv 2 \pmod 3$ with neither kernel prime equal to $3$ from the residual `five_no_two_prime_squarefree_index`.
-- source:
--   Dris conjecture k=5 branch of the Odd Perfect Number Conjecture mission. Mirror of the proved target OddPerfectNumber.Kernel.five_two_prime_cyclotomic_split (theorem_id 81a70179-c0e7-41e8-97bd-86af2cb90f91), which states the same split for the first block p^2+p+1. Cyclotomic factorisation sigma(p^5) = (p+1)(p^2+p+1)(p^2-p+1).

import Mathlib

namespace OddPerfectNumber.Kernel

/-- In the $k=5$ two-prime square-free-index case the SECOND cyclotomic block
`p^2 - p + 1` is `q x^2` or `r x^2`, exactly as the proved
`five_two_prime_cyclotomic_split` says for the first block `p^2 + p + 1`. -/
theorem five_two_prime_cyclotomic_split_second (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime)
    (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 =
          (2 * (p ^ 2 - p + 1) * ((p + 1) / 2 * (p ^ 2 + p + 1))) * (d1 ^ 2 * (q * r))) :
    (∃ x, p ^ 2 - p + 1 = q * x ^ 2) ∨ (∃ x, p ^ 2 - p + 1 = r * x ^ 2) := by
  sorry

end OddPerfectNumber.Kernel
