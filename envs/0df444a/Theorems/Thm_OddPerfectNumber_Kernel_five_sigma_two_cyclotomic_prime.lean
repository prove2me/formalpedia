-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_sigma_two_cyclotomic_prime
-- name    : OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_prime
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-29T15:09:43.635858+00:00
-- url     : https://prove2.me/theorems/d5e9b3e3-f3cf-42fd-9cb4-caee48f60c8b
-- title:
--   For prime p, sigma(p^5) = 2(p^2+p+1)((p+1)/2)(p^2-p+1)
-- statement:
--   For an odd prime $p$, the divisor sum of $p^5$ factors exactly as $\sigma(p^5) = 2UV$ with $U = p^2+p+1$ and $V = \frac{p+1}{2}(p^2-p+1)$. Since $p$ is an odd prime, $(p+1)/2$ is an exact integer and $\sigma(p^5) = (p^6-1)/(p-1) = (p+1)(p^2+p+1)(p^2-p+1)$, so the displayed identity holds. This is the correct statement of the factorisation: it requires $p$ prime. The primality hypothesis is necessary, since for a composite base such as $p = 9$ one has $\sigma(9^5) = 88573 \ne 2UV = 66430$, because $p^5$ then has divisors that are not powers of $p$.
-- source:
--   Dris conjecture, $k=5$ branch: the first equation $2m^2 = \sigma(p^5) s$ needs the exact factorisation $\sigma(p^5) = 2UV$. It follows from the elementary geometric series $(p^6-1)/(p-1) = (p+1)(p^2+p+1)(p^2-p+1)$ together with $p$ prime (so that $2 \mid p+1$ and the divisors of $p^5$ are exactly $1,p,\dots,p^5$). This corrects the earlier child `five_sigma_two_cyclotomic_odd` (theorem 789ef82d-9770-49cc-ab14-759c2a9e477a), which assumed only `hp : Odd p` and is therefore false: at $p = 9$ its two sides are $66430$ and $88573$.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_sigma_two_cyclotomic_prime (p : Nat) (hp : p.Prime) :
    2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) =
      ∑ d ∈ (p ^ 5).divisors, d := by
  sorry

end OddPerfectNumber.Kernel
