-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_2
-- name    : ManipPotential.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:09:21.661193+00:00
-- url     : https://prove2.me/theorems/dea30659-209f-4f54-b1ef-31c40e19ba96
-- title:
--   Theorem 4.2 — $\mathrm{MP}(\mathrm{PL}) = \lceil (n-1)/2 \rceil$
-- statement:
--   Let $m \ge 3$ candidates and $n \ge 2$ voters. The manipulation potential of plurality is
--   $$\mathrm{MP}(\mathrm{PL}) = \left\lceil \frac{n-1}{2} \right\rceil .$$
--   Further, $\mathrm{PL}$ is not $k$-ASP for any $0 \le k < \lceil (n-1)/2 \rceil$: for each such $k$ there are a tiebreaker, a profile of $n$ voters, a voter and a manipulation that she strictly prefers to adding $k$ copies of her truthful vote.
--
--   Since $k$-augmentation strategyproofness is not monotone in $k$, the second sentence is stronger than the lower bound $\mathrm{MP}(\mathrm{PL}) \ge \lceil (n-1)/2 \rceil$. Plurality's manipulation potential is about half of the bound $n-1$ that holds for every majority-consistent rule.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - encoding: ⌈(n−1)/2⌉ → Nat.ceil of the real (n − 1)/2; reason: Lean convention; the same natural number
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.2, p.11

import Mathlib
import Definitions.Def_ManipPotential_Supplement_plurality
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

namespace ManipPotential.Supplement

/-- Theorem 4.2 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.11): the manipulation potential of plurality is
`MP(PL) = ⌈(n − 1)/2⌉`; further, `PL` is not `k`-ASP for any `0 ≤ k < ⌈(n − 1)/2⌉`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `MP` and `k`-ASP are at the fixed electorate size `n` (`manipPotentialSCCAt`, `IsKASPAtSCC`: maximum, resp. for all, over the `m!` tiebreakers). The ceiling is `Nat.ceil` of the real `(n − 1)/2`. -/
theorem theorem_4_2 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) :
    manipPotentialSCCAt (plurality (m := m)) n = ((⌈((n : ℝ) - 1) / 2⌉₊ : ℕ) : ℕ∞) ∧
      ∀ k : ℕ, k < ⌈((n : ℝ) - 1) / 2⌉₊ → ¬ IsKASPAtSCC (plurality (m := m)) n k := by sorry

end ManipPotential.Supplement
