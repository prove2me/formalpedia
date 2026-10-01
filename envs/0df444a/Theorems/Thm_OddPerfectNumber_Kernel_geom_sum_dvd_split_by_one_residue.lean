-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_geom_sum_dvd_split_by_one_residue
-- name    : OddPerfectNumber.Kernel.geom_sum_dvd_split_by_one_residue
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T16:49:38.447098+00:00
-- url     : https://prove2.me/theorems/31abdc87-a3f3-4500-bc8c-77adbd906dd1
-- title:
--   A prime divisor of a geometric sum either is one modulo p or gives a nontrivial odd order
-- statement:
--   Let p be a prime, q a natural number with p not dividing q, and e a natural number. If p divides the sum of the first 2e+1 powers of q, then either q is congruent to 1 modulo p and p divides 2e+1, or q is not congruent to 1 modulo p and the multiplicative order of q in the cyclic group modulo p divides 2e+1.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem geom_sum_dvd_split_by_one_residue {p q e : Nat} (hp : p.Prime) (hpq : Not (Dvd.dvd p q))
    (hdvd : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)) :
    ((q : ZMod p) = 1) ∨ Dvd.dvd (2 * e + 1) (orderOf (q : ZMod p)) := by
  sorry

end OddPerfectNumber.Kernel
