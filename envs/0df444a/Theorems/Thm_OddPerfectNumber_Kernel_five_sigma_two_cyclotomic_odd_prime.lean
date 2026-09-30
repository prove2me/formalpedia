-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_sigma_two_cyclotomic_odd_prime
-- name    : OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd_prime
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T15:13:45.218726+00:00
-- url     : https://prove2.me/theorems/7f2041ff-30b4-4c8d-ad98-798dc15b91e1
-- title:
--   For odd prime p, sigma(p^5) = 2(p^2+p+1)((p+1)/2)(p^2-p+1)
-- statement:
--   For an odd prime $p$, the divisor sum of $p^5$ factors exactly as $\sigma(p^5) = 2UV$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$. Since $p$ is an odd prime, $(p+1)/2$ is an exact integer, the divisors of $p^5$ are exactly $1,p,\dots,p^5$, and $\sigma(p^5) = (p+1)(p^2+p+1)(p^2-p+1)$. This is the exact factorisation needed by the first Dris equation $2m^2 = \sigma(p^5) s$ on the $k=5$ branch. The hypotheses $p$ prime and $p \neq 2$ are both necessary: for the composite base $p = 9$ the two sides are $66430$ and $88573$, and for the even prime $p = 2$ they are $42$ and $63$.
-- source:
--   Dris conjecture, $k=5$ branch: the first equation $2m^2 = \sigma(p^5) s$ needs the exact factorisation $\sigma(p^5) = 2UV$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$. It follows from the elementary geometric series $\sigma(p^5) = \frac{p^6-1}{p-1} = (p+1)(p^2+p+1)(p^2-p+1)$ together with $p$ an odd prime, so that $2 \mid p+1$ and the divisors of $p^5$ are exactly its six powers. This supersedes two malformed earlier children: `five_sigma_two_cyclotomic_odd` (789ef82d-9770-49cc-ab14-759c2a9e477a), false for composite $p$, and `five_sigma_two_cyclotomic_prime` (d5e9b3e3-f3cf-42fd-9cb4-caee48f60c8b), false at $p = 2$.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_sigma_two_cyclotomic_odd_prime (p : Nat) (hp : p.Prime) (hp2 : p != 2) :
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d := by
  sorry

end OddPerfectNumber.Kernel
