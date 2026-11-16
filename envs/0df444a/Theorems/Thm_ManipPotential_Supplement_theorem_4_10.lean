-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_10
-- name    : ManipPotential.Supplement.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:14:54.433221+00:00
-- url     : https://prove2.me/theorems/18ba01f7-0b00-46f0-8e40-ba32f55c4490
-- title:
--   Theorem 4.10 — $\mathrm{MP}(\mathrm{BL}) = n-1$
-- statement:
--   Let $m \ge 3$ candidates and $n \ge 2$ voters.
--
--   1. (Upper bound.) $\mathrm{MP}(\mathrm{BL}) \le n - 1$.
--   2. (Lower bound.) If $m \ge 4$ and $n$ is odd, then
--   $$\mathrm{MP}(\mathrm{BL}) = n - 1,$$
--   and Black's Rule is not $k$-ASP for any $0 \le k < n - 1$.
--
--   Adding the Condorcet conditional to Borda Count moves the manipulation potential from one that grows with $m$ to the largest one a Condorcet extension can have.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - reading: '(lower bound assumes m ≥ 4 and odd n)', next to 'Further, BL is not k-ASP for any 0 ≤ k < n − 1' → the assumptions on the equality and on the 'not k-ASP' clause; the upper bound at every n ≥ 2; reason: Section 4, 'Proof Structure' (p.10) states that the lower-bound or divisibility requirements are used to construct the lower-bound profiles; the proof derives the upper bound with no assumption and both the lower bound and the 'not k-ASP' sentence from the construction; Appendix A.3 (p.50) proves both from one profile with groups of size (n − 1)/2
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.10, p.19 (restated in Appendix A.3, p.50)

import Mathlib
import Definitions.Def_ManipPotential_Supplement_blackRule
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

namespace ManipPotential.Supplement

/-- Theorem 4.10 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.19; restated in Appendix A.3, p.50): the manipulation potential of
Black's Rule is `MP(BL) = n − 1` (lower bound assumes `m ≥ 4` and odd `n`); further, `BL` is not
`k`-ASP for any `0 ≤ k < n − 1`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `MP` and `k`-ASP are at the fixed electorate size `n` (`manipPotentialSCCAt`, `IsKASPAtSCC`: maximum, resp. for all, over the `m!` tiebreakers). The upper bound holds at every `n ≥ 2` (Claim 4.1); the equality
and the "not `k`-ASP" clause are stated under `m ≥ 4` and odd `n`, as in the proof (Appendix A.3). -/
theorem theorem_4_10 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) :
    manipPotentialSCCAt (blackRule (m := m)) n ≤ ((n - 1 : ℕ) : ℕ∞) ∧
    (4 ≤ m → Odd n →
      manipPotentialSCCAt (blackRule (m := m)) n = ((n - 1 : ℕ) : ℕ∞) ∧
      ∀ k : ℕ, k < n - 1 → ¬ IsKASPAtSCC (blackRule (m := m)) n k) := by sorry

end ManipPotential.Supplement
