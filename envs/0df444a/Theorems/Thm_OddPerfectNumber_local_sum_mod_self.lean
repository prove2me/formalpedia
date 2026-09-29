-- Prove2me | Theorems.Thm_OddPerfectNumber_local_sum_mod_self
-- name    : OddPerfectNumber.local_sum_mod_self
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:57:33.112554+00:00
-- url     : https://prove2.me/theorems/19cfb5f7-44f5-4961-86e6-227e33ac43b7
-- title:
--   Local geometric sum is one mod its base
-- statement:
--   A local geometric sum $1 + r + \cdots + r^{2a}$ at a prime $r$ is congruent to $1$ modulo $r$. Hence the $r$-adic valuation of the $r$-local factor vanishes -- the fact that lets an $r$-adic count skip the $r$-term.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem local_sum_mod_self (r a : Nat) (hr : r.Prime) :
    (∑ i ∈ Finset.range (2 * a + 1), r ^ i) % r = 1 := by
  sorry

end OddPerfectNumber
