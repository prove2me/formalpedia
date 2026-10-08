-- Prove2me | Theorems.Thm_Helfgott_three_odd_primes_of_weighted_count
-- name    : Helfgott.three_odd_primes_of_weighted_count
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:21:59.592686+00:00
-- url     : https://prove2.me/theorems/890fb2cc-ecec-4694-ba36-318f94dd29f4
-- title:
--   Extracting three odd primes from a weighted count
-- statement:
--   For N ≥ 10^27, if the signed von Mangoldt ternary count with |a|≤1.079955 and |b|≤1.414 is at least N²/2500, then N is a sum of three odd primes. The weighted lower bound is a hypothesis: it remains to be established by the analytic major- and minor-arc estimates. This theorem supplies the final extraction step without assuming the smoothing is nonnegative.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (7.3), (7.19), (7.49)–(7.50), https://arxiv.org/abs/1312.7748 . Elementary replacement for the prime-power removal estimates in the concluding argument. Written by Codex.

import Definitions.Def_Helfgott_PrimePowerRemoval
open scoped BigOperators

namespace Helfgott

theorem three_odd_primes_of_weighted_count (a b : ℕ → ℝ)
    (ha : ∀ n, |a n| ≤ (1079955 / 1000000 : ℝ))
    (hb : ∀ n, |b n| ≤ (707 / 500 : ℝ)) (N : ℕ) (hN : 10 ^ 27 ≤ N)
    (hcount : (1 / 2500 : ℝ) * (N : ℝ) ^ 2 ≤
      ∑ t ∈ tripleIndices N, weightedTripleTerm a b t) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ N = p + q + r := by sorry

end Helfgott
