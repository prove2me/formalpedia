-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_dvd_branch_split
-- name    : OddPerfectNumber.geom_sum_dvd_branch_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:43:18.022203+00:00
-- url     : https://prove2.me/theorems/dde59f87-3bce-4fc4-96c4-afdd7de81c07
-- title:
--   A prime divisor of an odd geometric sum enters either as a one residue or through a nontrivial odd order
-- statement:
--   Let p be a prime and q a natural number with p not dividing q, and e a natural number. If p divides the sum of the first two e plus one powers of q, then either q is congruent to 1 modulo p and p divides two e plus one, or q is not congruent to 1 modulo p and the multiplicative order of q modulo p is greater than 1 and divides two e plus one.

import Mathlib

namespace OddPerfectNumber

theorem geom_sum_dvd_branch_split {p q e : Nat} (hp : p.Prime) (hpq : Not (Dvd.dvd p q))
    (hdvd : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)) :
    ((q : ZMod p) = 1 ∧ Dvd.dvd p (2 * e + 1)) ∨
      ((q : ZMod p) ≠ 1 ∧ 1 < orderOf (q : ZMod p) ∧
        Dvd.dvd (orderOf (q : ZMod p)) (2 * e + 1)) := by
  sorry

end OddPerfectNumber
