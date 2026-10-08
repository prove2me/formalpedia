-- Prove2me | Theorems.Thm_Helfgott_bad_weighted_triples_le
-- name    : Helfgott.bad_weighted_triples_le
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:21:46.668067+00:00
-- url     : https://prove2.me/theorems/651d343d-3cfa-40d4-9f37-c1a183d3f411
-- title:
--   Elementary ternary prime-power removal bound
-- statement:
--   For N ≥ 10^27 and real weights with |a(n)| ≤ 1.079955 and |b(n)| ≤ 1.414, the contribution from triples that fail to be three odd primes is at most N²/5000. The weights may be signed. This is an elementary replacement for the prime-power removal step in Helfgott’s final argument, with a weaker but sufficient constant.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (7.3), (7.19), (7.49)–(7.50), https://arxiv.org/abs/1312.7748 . Elementary replacement for the prime-power removal estimates in the concluding argument. Written by Codex.

import Definitions.Def_Helfgott_PrimePowerRemoval
open scoped BigOperators

namespace Helfgott

theorem bad_weighted_triples_le (a b : ℕ → ℝ)
    (ha : ∀ n, |a n| ≤ (1079955 / 1000000 : ℝ))
    (hb : ∀ n, |b n| ≤ (707 / 500 : ℝ)) (N : ℕ) (hN : 10 ^ 27 ≤ N) :
    ∑ t ∈ badTripleIndices N, weightedTripleTerm a b t
      ≤ (1 / 5000 : ℝ) * (N : ℝ) ^ 2 := by sorry

end Helfgott
