-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_mul_perfect
-- name    : OddPerfectNumber.sigma_mul_perfect
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:17:00.241988+00:00
-- url     : https://prove2.me/theorems/fadb8b05-5488-4fb7-ad42-c51d64f9abc4
-- title:
--   Packaged coprime data give a perfect number
-- statement:
--   If $a$ and $b$ are coprime with divisor sums $s_a, s_b$ satisfying $s_a s_b = 2ab$ and $ab > 0$, then $ab$ is perfect. Multiplicativity of $\sigma$ plus the packaged equation gives $\sigma(ab) = 2ab$. This single lemma covers the perfectness opening of every packaged Dris argument in any cofactor shape.
-- source:
--   Dris cofactor analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem sigma_mul_perfect (a b sa sb : Nat) (hcop : Nat.Coprime a b)
    (hpos : 0 < a * b)
    (ha : (∑ x ∈ a.divisors, x) = sa)
    (hb : (∑ x ∈ b.divisors, x) = sb)
    (h : sa * sb = 2 * (a * b)) :
    Nat.Perfect (a * b) := by
  sorry

end OddPerfectNumber
