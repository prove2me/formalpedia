-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_succ
-- name    : OddPerfectNumber.geom_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:13:59.365625+00:00
-- url     : https://prove2.me/theorems/5ff82cdc-d731-4571-b034-93012497c1b7
-- title:
--   Peeling a geometric sum
-- statement:
--   Peeling the constant term off a geometric sum: $1 + q + \cdots + q^n = q(1 + \cdots + q^{n-1}) + 1$. Extracted as a standalone lemma from the accepted proof of $\mathtt{no\_dris\_five\_s\_odd\_eq\_three}$ (DHP toolkit).
-- source:
--   DHP toolkit of the accepted Prove2Me proof of OddPerfectNumber.no_dris_five_s_odd_eq_three; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem geom_succ (q n : Nat) :
    ∑ i ∈ Finset.range (n + 1), q ^ i = q * (∑ i ∈ Finset.range n, q ^ i) + 1 := by
  sorry

end OddPerfectNumber
