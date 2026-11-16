-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_4
-- name    : ManipPotential.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:11:10.934483+00:00
-- url     : https://prove2.me/theorems/87872c4f-70f3-4182-aa40-6c75a9529e93
-- title:
--   Theorem 4.4 — $\mathrm{MP}(\mathrm{BC}) = m-2$
-- statement:
--   Let $m \ge 3$ candidates and $n \ge 2$ voters.
--
--   1. (Upper bound.) $\mathrm{MP}(\mathrm{BC}) \le m - 2$.
--   2. (Lower bound.) If $n$ is even, then
--   $$\mathrm{MP}(\mathrm{BC}) = m - 2,$$
--   and Borda Count is not $k$-ASP for any $0 \le k < m - 2$.
--
--   Unlike plurality and the runoff rules, the manipulation potential of Borda Count does not grow with the number of voters.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - reading: '(lower bound assumes n is even)', next to 'Further, BC is not k-ASP for any 0 ≤ k < m − 2' → n even on the equality and on the 'not k-ASP' clause; the upper bound at every n ≥ 2; reason: Section 4, 'Proof Structure' (p.10) states that the lower-bound or divisibility requirements are used to construct the lower-bound profiles; the proof derives the upper bound with no assumption and both the lower bound and the 'not k-ASP' sentence from the construction
--   - encoding: Borda points m − j → normalized Borda vector (m − j)/(m − 1); reason: p.15: scaling by 1/(m − 1) does not change the output
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.4, p.13

import Mathlib
import Definitions.Def_ManipPotential_Supplement_borda
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

namespace ManipPotential.Supplement

/-- Theorem 4.4 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.13): the manipulation potential of Borda Count is `MP(BC) = m − 2`
(lower bound assumes `n` is even); further, `BC` is not `k`-ASP for any `0 ≤ k < m − 2`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `MP` and `k`-ASP are at the fixed electorate size `n` (`manipPotentialSCCAt`, `IsKASPAtSCC`: maximum, resp. for all, over the `m!` tiebreakers). The upper bound `MP ≤ m − 2` holds at every `n ≥ 2`; the equality
and the "not `k`-ASP" clause are stated for even `n`, as in the proof (p.13). -/
theorem theorem_4_4 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) :
    manipPotentialSCCAt (borda (m := m)) n ≤ ((m - 2 : ℕ) : ℕ∞) ∧
    (Even n →
      manipPotentialSCCAt (borda (m := m)) n = ((m - 2 : ℕ) : ℕ∞) ∧
      ∀ k : ℕ, k < m - 2 → ¬ IsKASPAtSCC (borda (m := m)) n k) := by sorry

end ManipPotential.Supplement
