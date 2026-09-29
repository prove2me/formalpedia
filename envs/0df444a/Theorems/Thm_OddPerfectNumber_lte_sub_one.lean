-- Prove2me | Theorems.Thm_OddPerfectNumber_lte_sub_one
-- name    : OddPerfectNumber.lte_sub_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:13:55.719551+00:00
-- url     : https://prove2.me/theorems/11776326-139e-4deb-904c-fa84315e6399
-- title:
--   LTE splitting for x^n - 1
-- statement:
--   Lifting-the-exponent for $x^n - 1$ at an odd prime $q$ dividing $x - 1$: the $q$-adic valuation splits additively. Extracted as a standalone lemma from the accepted proof of $\mathtt{no\_dris\_five\_s\_odd\_eq\_three}$ (DHP toolkit); the key analytic input for order arguments on the OPN cores.
-- source:
--   DHP toolkit of the accepted Prove2Me proof of OddPerfectNumber.no_dris_five_s_odd_eq_three; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem lte_sub_one {q x n : Nat} (hq : q.Prime) (hq2 : q ≠ 2) (hx : 1 < x)
    (hqx : q ∣ x - 1) (hn : n ≠ 0) :
    padicValNat q (x ^ n - 1) = padicValNat q (x - 1) + padicValNat q n := by
  sorry

end OddPerfectNumber
