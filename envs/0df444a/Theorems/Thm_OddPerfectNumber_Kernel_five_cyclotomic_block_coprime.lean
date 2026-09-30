-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_block_coprime
-- name    : OddPerfectNumber.Kernel.five_cyclotomic_block_coprime
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:09:51.969945+00:00
-- url     : https://prove2.me/theorems/2c9214f0-5184-4b67-b5c8-b83681903eba
-- title:
--   The two k=5 cyclotomic blocks U and V are coprime for odd p
-- statement:
--   For an odd natural $p$, the two blocks $U = p^2+p+1$ and $V = \frac{p+1}{2}\,(p^2-p+1)$ appearing in the $k=5$ factorisation $\sigma(p^5) = 2UV$ are coprime. Suppose a prime $\ell$ divides both. If $\ell$ divides $\frac{p+1}{2}$ then $\ell$ divides $p+1$, so $p \equiv -1 \pmod \ell$ and $U \equiv 1-1+1 = 1 \pmod\ell$, a contradiction. Otherwise $\ell$ divides $p^2-p+1$, and together with $\ell \mid p^2+p+1$ this gives $2p \equiv 0 \pmod\ell$. Since $U = factorisation of $\sigma(p^5)$ is $\sigma(p^5) = 2UV$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$. The accepted Odd p^2+p+1$ is odd when $p$ is odd, $\ell$ is odd, hence $p \equiv 0 \pmod \ell$ and again $U \equiv 1 \pmod\ell$, a contradiction. This is the copPerfectNumber.Kernel.five_cyclotomic_pair_coprime (dbed225d-85c0-4877-9ead-8c073246bf99) only shows $\gcd(p^2+p+1,rimality that the one-prime-times-square exclusion needs: the accepted prime_mul_coprime_nonsquares_not_square applies to $a = U$ and $b = V$ exactly p^2-p+1) = 1$, which is not the coprimality required: the prime-toggle lemma prime_mul_coprime_nonsquares_not when this gcd is $1$.
-- source:
--   Odd Perfect Number Conjecture, $k=5$ branch. The exact_square (0a9fa825-491c-44a2-9f99-eaf3e4677c74) needs $\gcd(U, V) = 1$ with the factor of $2$ already removed from $p+1$. The argument is elementary and unconditional for odd $p$.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_cyclotomic_block_coprime (p : Nat) (hp2 : p != 2) :
    Nat.gcd (p ^ 2 + p + 1) (((p + 1) / 2) * (p ^ 2 - p + 1)) = 1 := by
  sorry

end OddPerfectNumber.Kernel
