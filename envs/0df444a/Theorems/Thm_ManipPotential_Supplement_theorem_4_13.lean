-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_13
-- name    : ManipPotential.Supplement.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:16:27.953072+00:00
-- url     : https://prove2.me/theorems/cce2621a-d341-4f39-a256-ab02d31ff1b1
-- title:
--   Theorem 4.13 — faithful neutral majoritarian rules have $\mathrm{MP} \ge n-2$
-- statement:
--   Let $m \ge 3$ candidates and $n \ge 2$ voters, and let $F$ be a faithful and neutral majoritarian SCC. Then
--   $$\mathrm{MP}(F) \ge n - 2,$$
--   and $F$ is not $k$-ASP for any $k < n - 2$.
--
--   Together with the upper bound $n-1$ for majority-consistent rules, majoritarian Condorcet extensions cannot do much better than the worst case for Condorcet extensions.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - generalization: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅, for every SCC F; reason: the Lean statement also covers SCCs with empty winner sets; for an SCC with nonempty outputs it is the paper's statement
--   - reading: majoritarian, 'for any two profiles ≻_N, ≻′_N' with equal margin signs, F(≻_N) = F(≻′_N) → IsMajoritarian compares profiles of any two lengths; reason: the proof (p.21) uses F_T(≻′_1, ≻_{−1}) = F_T(≻′_1), comparing an n-voter profile with a one-voter profile, and footnote 8 (p.8) defines rules on profiles of every length
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.13, p.21

import Mathlib
import Definitions.Def_ManipPotential_Supplement_IsFaithfulSCC
import Definitions.Def_ManipPotential_Supplement_IsNeutral
import Definitions.Def_ManipPotential_Supplement_IsMajoritarian
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

namespace ManipPotential.Supplement

/-- Theorem 4.13 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.21): any faithful and neutral majoritarian SCC `F` has
`MP(F) ≥ n − 2`; further, `F` is not `k`-ASP for any `k < n − 2`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `MP` and `k`-ASP are at the fixed electorate size `n` (`manipPotentialSCCAt`, `IsKASPAtSCC`: maximum, resp. for all, over the `m!` tiebreakers). Majoritarianism compares profiles of any lengths; faithfulness is
about one-ballot profiles. No nonemptiness of `F` is assumed: on an empty winner set the tie-broken
rule returns the tiebreaker's top candidate (`tieBreak`). -/
theorem theorem_4_13 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) (F : SCC m) (hF : IsFaithfulSCC F) (hN : IsNeutral F)
    (hM : IsMajoritarian F) :
    ((n - 2 : ℕ) : ℕ∞) ≤ manipPotentialSCCAt F n ∧
      ∀ k : ℕ, k < n - 2 → ¬ IsKASPAtSCC F n k := by sorry

end ManipPotential.Supplement
