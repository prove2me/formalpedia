-- Prove2me | Theorems.Thm_OddPerfectNumber_three_geom_sum_prime_power_index_prime_v2
-- name    : OddPerfectNumber.three_geom_sum_prime_power_index_prime_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T17:25:47.075283+00:00
-- url     : https://prove2.me/theorems/7280a4ee-bae6-437f-82ab-0fcc2772b060
-- title:
--   prime-power geometric sum has prime index, base above one
-- statement:
--   If the length-t base-b geometric sum with 1<b is a prime power r^beta with t odd > 1, then t is prime. (v1 omitted the 1<b premise and was false: b=1,t=9 gives sum 9=3^2 with t composite.)
-- source:
--   Corrected shared elementary lemma for q17/q31/37..61 finite branches; v1 quarantined as false.

import Mathlib

namespace OddPerfectNumber

theorem three_geom_sum_prime_power_index_prime_v2 (b t r beta : Nat) (hb : 1 < b) (ht : 1 < t) (hodd : Odd t)
    (hr : r.Prime) (hβ : 0 < beta)
    (hgeom : (Finset.range t).sum (fun i => b ^ i) = r ^ beta) : t.Prime := by
  sorry

end OddPerfectNumber
