-- Prove2me | Theorems.Thm_OddPerfectNumber_dvd_succ_of_sigma_dvd
-- name    : OddPerfectNumber.dvd_succ_of_sigma_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T08:58:59.819334+00:00
-- url     : https://prove2.me/theorems/309504ba-148d-4612-924e-55012065200a
-- title:
--   A divisor-sum divisibility forces q to divide k + 1
-- statement:
--   Let $p$ and $q$ be primes with $q$ odd, let $a \ne 0$, and suppose $q^2$ divides the geometric sum $1 + p + \cdots + p^k$ while the divisor sum $\sigma(q^{2a}) = 1 + q + \cdots + q^{2a}$ divides $p^k$. Then $q \mid k + 1$. The argument lifts the exponent in $p^{k+1} - 1$ at $q$, identifies the exact valuation contribution, and reads off the order of $p$ modulo $q$ through cyclotomic means. This order extraction is the key step that turns local divisor-sum divisibility into a global congruence restriction on the special exponent. Extracted (with gratitude) from the local toolkit of the accepted proof of the $s = 3$ Dris case at special exponent $k = 5$.
-- source:
--   Local DHP toolkit of the accepted Prove2Me proof of OddPerfectNumber.no_dris_five_s_odd_eq_three (lifting-the-exponent/order argument in the style of Dandapat-Hunsucker-Pomerance); Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem dvd_succ_of_sigma_dvd (p k q a : Nat) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (ha : a ≠ 0)
    (hq2S : q ^ 2 ∣ ∑ i ∈ Finset.range (k + 1), p ^ i)
    (hdvd : (∑ i ∈ Finset.range (2 * a + 1), q ^ i) ∣ p ^ k) : q ∣ k + 1 := by
  sorry

end OddPerfectNumber
