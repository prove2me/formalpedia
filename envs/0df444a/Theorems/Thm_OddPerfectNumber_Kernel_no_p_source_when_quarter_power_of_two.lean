-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_no_p_source_when_quarter_power_of_two
-- name    : OddPerfectNumber.Kernel.no_p_source_when_quarter_power_of_two
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T03:15:48.311885+00:00
-- url     : https://prove2.me/theorems/0f8e92a1-0c4a-4d87-98eb-c316f01008d4
-- title:
--   No incoming $p$-source when $(p-1)/4$ is a power of two
-- statement:
--   Let $p\equiv1\pmod4$ be prime with $p\ge5$, and suppose $(p-1)/4$ is a power of two. Then no prime $t$ can satisfy $p \mid 1+t+\dots+t^{2e}$.
--
--   **Proof.** $p\mid 1+t+\dots+t^{2e}$ gives $(t-1)(1+t+\dots+t^{2e}) = t^{2e+1}-1$, so $t^{2e+1}\equiv1\pmod p$ and $d=\operatorname{ord}_p(t) \mid 2e+1$; in particular $d$ is odd. By Fermat $d\mid p-1$, and since $4\mid p-1$ and $d$ is odd, $\gcd(d,4)=1$ forces $d\mid (p-1)/4$. If $(p-1)/4=2^k$ then $d$ is a power of two and also odd, so $d=1$, i.e. $t\equiv1\pmod p$. But then $1+t+\dots+t^{2e}\equiv 2e+1$, and the proved theorem `sigma_square_at_one_mod_p_not_dvd_p` forbids $p$ from dividing $1+t+t^2$ when $t\equiv1$. Hence $t\equiv1$, which is the only possibility.
--
--   **Consequence.** The second Dris equation $h_2$ requires an incoming source of $p$, since $p^5 \mid \sigma(m^2)$. For primes $p\equiv1\pmod4$ with $(p-1)/4$ a power of two this is impossible, so those $p$ are eliminated. Numerically, for $p<4000$ the eliminated primes are exactly $5$, $17$ and $257$ — in particular **$p=5$ is ruled out**, and $17$ survives neither. Primes with an odd factor in $(p-1)/4$ (e.g. $13,29,37,53,61,\dots$) are unaffected.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- If `p = 1 (mod 4)` and `(p-1)/4` is a power of two, then a prime `t` dividing the
three-term sum must satisfy `t = 1 (mod p)`. -/
theorem no_p_source_when_quarter_power_of_two (p t e k : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : t.Prime) (hquart : (p - 1) / 4 = 2 ^ k)
    (hdiv : (p : Nat) ∣ 1 + t + t ^ (2 * e)) :
    (t : ZMod p) = 1 := by
  sorry

end OddPerfectNumber.Kernel
