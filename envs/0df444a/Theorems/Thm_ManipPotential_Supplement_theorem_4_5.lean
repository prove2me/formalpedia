-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_5
-- name    : ManipPotential.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:12:05.143194+00:00
-- url     : https://prove2.me/theorems/50f0d8c9-a546-4b30-86b9-eebf7adace28
-- title:
--   Theorem 4.5 — $s_1 = s_2$ implies $\mathrm{MP}(F^s) = \infty$
-- statement:
--   Let $m \ge 3$, $n \ge 2$, and let $s$ be a positional scoring vector ($1 = s_1 \ge s_2 \ge \dots \ge s_m = 0$) with $s_1 = s_2$. Then
--   $$\mathrm{MP}(F^s) = \infty,$$
--   and in particular $F^s$ is not $k$-ASP for any $k \ge 0$.
--
--   If a scoring rule treats the top two positions equally, adding copies of a voter cannot lift her top choice over her second choice, while a misreport can.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - encoding: s = (s_j)_{j∈[m]}, 1-based → s : Fin m → ℝ, 0-based, with s₁, s₂ read through the 1-based scoreAt; reason: Lean indexing; same vectors
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.5, p.15

import Mathlib
import Definitions.Def_ManipPotential_Supplement_IsScoringVector
import Definitions.Def_ManipPotential_Supplement_scoreAt
import Definitions.Def_ManipPotential_Supplement_scoringRule
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

namespace ManipPotential.Supplement

/-- Theorem 4.5 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.15): for any positional scoring rule `F^s` with `s₁ = s₂`,
`MP(F^s) = ∞`; in particular, `F^s` is not `k`-ASP for any `k ≥ 0`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `MP` and `k`-ASP are at the fixed electorate size `n` (`manipPotentialSCCAt`, `IsKASPAtSCC`: maximum, resp. for all, over the `m!` tiebreakers). `s₁, s₂` are the 1-based entries `scoreAt s 1`, `scoreAt s 2`. -/
theorem theorem_4_5 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) (s : Fin m → ℝ) (hs : IsScoringVector s)
    (h12 : scoreAt s 1 = scoreAt s 2) :
    manipPotentialSCCAt (scoringRule s) n = ⊤ ∧
      ∀ k : ℕ, ¬ IsKASPAtSCC (scoringRule s) n k := by sorry

end ManipPotential.Supplement
