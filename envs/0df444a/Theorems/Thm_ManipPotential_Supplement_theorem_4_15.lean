-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_15
-- name    : ManipPotential.Supplement.theorem_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:17:00.918042+00:00
-- url     : https://prove2.me/theorems/c1e8b8e9-8238-4d4d-8d7d-8bdaa40ce915
-- title:
--   Theorem 4.15 — biranking-majority-consistent rules have $\mathrm{MP} \ge (n-1)/2$ for odd $n$
-- statement:
--   Let $m \ge 3$ candidates and let $n \ge 2$ be odd. Every anonymous biranking-majority-consistent social choice function $f$ satisfies
--   $$\mathrm{MP}(f) \ge \frac{n-1}{2} .$$
--
--   Since runoff rules and Condorcet extensions are biranking-majority-consistent, the manipulation potential of plurality is essentially the best these classes can achieve, and Borda Count has a much lower one when $n \gg m$.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.15, p.22

import Mathlib
import Definitions.Def_ManipPotential_Anonymous
import Definitions.Def_ManipPotential_manipPotentialAt
import Definitions.Def_ManipPotential_Supplement_IsBirankingMajorityConsistent

namespace ManipPotential.Supplement

/-- Theorem 4.15 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.22): whenever `n` is odd, any anonymous biranking-majority-consistent
SCF `f` has `MP(f) ≥ (n − 1)/2`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions; with `n` odd,
`(n − 1)/2` is an exact natural-number quotient. `MP` is the published `manipPotentialAt` of the
SCF at electorate size `n`, and anonymity the published `Anonymous`. The theorem has no
"not `k`-ASP for every smaller `k`" clause (footnote 10, p.9). -/
theorem theorem_4_15 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) (f : List (Ranking m) → Fin m) (hA : Anonymous f)
    (hB : IsBirankingMajorityConsistent f) (hodd : Odd n) :
    (((n - 1) / 2 : ℕ) : ℕ∞) ≤ manipPotentialAt f n := by sorry

end ManipPotential.Supplement
