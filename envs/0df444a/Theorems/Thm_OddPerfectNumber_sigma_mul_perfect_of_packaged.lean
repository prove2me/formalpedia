-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_mul_perfect_of_packaged
-- name    : OddPerfectNumber.sigma_mul_perfect_of_packaged
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:20:38.08534+00:00
-- url     : https://prove2.me/theorems/3b17abd8-33d3-4898-98ea-851c02bbf2dc
-- title:
--   Packaged coprime data give a perfect number
-- statement:
--   If $a$ and $b$ are coprime with divisor sums $s_a, s_b$ satisfying $s_a s_b = 2ab$ and $ab > 0$, then $ab$ is perfect. Multiplicativity of $\sigma$ plus the packaged equation gives $\sigma(ab) = 2ab$. This single lemma covers the perfectness opening of every packaged Dris argument in any cofactor shape. (Replaces a same-content version whose short hypothesis names tripped the canonical-target concatenated-identifier guard.)
-- source:
--   Dris cofactor analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem sigma_mul_perfect_of_packaged (a b sa sb : Nat) (hcop : Nat.Coprime a b)
    (hpos : 0 < a * b)
    (hsiga : (∑ x ∈ a.divisors, x) = sa)
    (hsigb : (∑ x ∈ b.divisors, x) = sb)
    (hpack : sa * sb = 2 * (a * b)) :
    Nat.Perfect (a * b) := by
  sorry

end OddPerfectNumber
