-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
-- name    : OddPerfectNumber.geom_mul_sub_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:13:56.612393+00:00
-- url     : https://prove2.me/theorems/069159f8-59c6-4023-af9d-5ad6dabcdf1b
-- title:
--   Telescoping product for geometric sums
-- statement:
--   Telescoping product for geometric sums: $(1 + p + \cdots + p^{n-1})(p - 1) = p^n - 1$. Extracted as a standalone lemma from the accepted proof of $\mathtt{no\_dris\_five\_s\_odd\_eq\_three}$ (DHP toolkit) so divisor-sum arguments can import it.
-- source:
--   DHP toolkit of the accepted Prove2Me proof of OddPerfectNumber.no_dris_five_s_odd_eq_three; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem geom_mul_sub_one (p n : Nat) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range n, p ^ i) * (p - 1) = p ^ n - 1 := by
  sorry

end OddPerfectNumber
