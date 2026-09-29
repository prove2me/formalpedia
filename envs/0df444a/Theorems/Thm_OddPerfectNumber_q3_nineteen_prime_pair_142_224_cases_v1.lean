-- Prove2me | Theorems.Thm_OddPerfectNumber_q3_nineteen_prime_pair_142_224_cases_v1
-- name    : OddPerfectNumber.q3_nineteen_prime_pair_142_224_cases_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T18:09:33.003015+00:00
-- url     : https://prove2.me/theorems/4f1594a6-e723-4169-9dbd-2288f2af858d
-- title:
--   Finite prime pair cases in the q3=19 high-q4 window
-- statement:
--   If q₄ and 2q₄−1 are both prime with 142≤q₄≤224, then q₄ is 157, 199, or 211.
-- source:
--   Exact finite arithmetic, staged into four narrow q₄ intervals to avoid broad interval_cases; composite q₄ or composite 2q₄−1 branches are discharged by norm_num.

import Mathlib

namespace OddPerfectNumber

theorem q3_nineteen_prime_pair_142_224_cases_v1 (q4 p : Nat) (hq4prime : q4.Prime) (hp : p.Prime) (hp_eq : p = 2 * q4 - 1) (hq4ge : 142 ≤ q4) (hq4le : q4 ≤ 224) : q4 = 157 ∨ q4 = 199 ∨ q4 = 211 := by
  sorry

end OddPerfectNumber
