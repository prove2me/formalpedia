-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_3
-- name    : ManipPotential.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:10:08.483577+00:00
-- url     : https://prove2.me/theorems/70018eb8-b69e-4ab7-a51f-f4c8c34f5338
-- title:
--   Theorem 4.3 — $\mathrm{MP}(\mathrm{PWR}) = \mathrm{MP}(\mathrm{IRV}) = n-1$
-- statement:
--   Let $m \ge 3$ candidates and $n \ge 2$ voters, and let Plurality with Runoff ($\mathrm{PWR}$) and Instant Runoff ($\mathrm{IRV}$) use parallel-universes tiebreaking.
--
--   1. (Upper bound.) $\mathrm{MP}(\mathrm{PWR}) \le n - 1$ and $\mathrm{MP}(\mathrm{IRV}) \le n - 1$.
--   2. (Lower bound.) If $m \ge 4$, $n \ge 5$ and $4 \mid n - 1$, then
--   $$\mathrm{MP}(\mathrm{PWR}) = \mathrm{MP}(\mathrm{IRV}) = n - 1,$$
--   and neither rule is $k$-ASP for any $0 \le k < n - 1$.
--
--   So the bound $n-1$ that every majority-consistent rule satisfies is attained by both runoff rules.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - reading: '(lower bound assumes m ≥ 4, n ≥ 5 and that n − 1 is divisible by 4)', next to 'Further, neither rule is k-ASP for any 0 ≤ k < n − 1' → the assumptions on the equality and on the 'not k-ASP' clause; the upper bound at every n ≥ 2; reason: Section 4, 'Proof Structure' (p.10) states that the lower-bound or divisibility requirements are used to construct the lower-bound profiles; the proof derives the upper bound with no assumption and both the lower bound and the 'not k-ASP' sentence from the construction
--   - reading: parallel-universes tiebreaking for PWR, 'the candidate with the higher score wins' the runoff → a tied runoff makes both finalists winners; reason: p.12 defines c ∈ PWR(≻_N) if some way of breaking ties makes c win; a runoff tie is a tie of the output, then broken by ≻_T
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.3, p.12

import Mathlib
import Definitions.Def_ManipPotential_Supplement_pluralityWithRunoff
import Definitions.Def_ManipPotential_Supplement_instantRunoff
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

namespace ManipPotential.Supplement

/-- Theorem 4.3 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.12): the manipulation potentials of Plurality with Runoff and Instant
Runoff are `MP(PWR) = MP(IRV) = n − 1` (lower bound assumes `m ≥ 4`, `n ≥ 5` and that `n − 1` is
divisible by `4`); further, neither rule is `k`-ASP for any `0 ≤ k < n − 1`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `MP` and `k`-ASP are at the fixed electorate size `n` (`manipPotentialSCCAt`, `IsKASPAtSCC`: maximum, resp. for all, over the `m!` tiebreakers). The upper bound `MP ≤ n − 1` holds at every `n ≥ 2`; the equality
and the "not `k`-ASP" clause are stated under the lower-bound assumptions, as in the proof (p.12).
Both rules use parallel-universes tiebreaking. -/
theorem theorem_4_3 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) :
    (manipPotentialSCCAt (pluralityWithRunoff (m := m)) n ≤ ((n - 1 : ℕ) : ℕ∞) ∧
      manipPotentialSCCAt (instantRunoff (m := m)) n ≤ ((n - 1 : ℕ) : ℕ∞)) ∧
    (4 ≤ m → 5 ≤ n → 4 ∣ n - 1 →
      manipPotentialSCCAt (pluralityWithRunoff (m := m)) n = ((n - 1 : ℕ) : ℕ∞) ∧
      manipPotentialSCCAt (instantRunoff (m := m)) n = ((n - 1 : ℕ) : ℕ∞) ∧
      ∀ k : ℕ, k < n - 1 →
        ¬ IsKASPAtSCC (pluralityWithRunoff (m := m)) n k ∧
          ¬ IsKASPAtSCC (instantRunoff (m := m)) n k) := by sorry

end ManipPotential.Supplement
