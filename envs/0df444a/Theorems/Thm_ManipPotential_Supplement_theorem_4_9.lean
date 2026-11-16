-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_9
-- name    : ManipPotential.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:13:55.025365+00:00
-- url     : https://prove2.me/theorems/18bd5a48-231c-42de-ba72-df5f5cc2655b
-- title:
--   Theorem 4.9 — every other scoring rule is beaten by $\mathrm{PL}$ or $\mathrm{BC}$
-- statement:
--   Let $m \ge 3$ and let $s$ be a positional scoring vector with $F^s \notin \{\mathrm{PL}, \mathrm{BC}\}$, i.e. $s \ne (1, 0, \dots, 0)$ and $s$ is not the normalized Borda vector. Let $n \ge 4$ be divisible by $4$. Then, with all manipulation potentials taken at $n$ voters,
--
--   1. $\mathrm{MP}(F^s) > \mathrm{MP}(\mathrm{BC})$ or $\mathrm{MP}(F^s) \ge \mathrm{MP}(\mathrm{PL})$;
--   2. if moreover $n \ge \max\bigl(8, \tfrac{2}{s_2} + 4\bigr)$, then $\mathrm{MP}(F^s) > \mathrm{MP}(\mathrm{BC})$ or $\mathrm{MP}(F^s) > \mathrm{MP}(\mathrm{PL})$.
--
--   So within the class of positional scoring rules, the smallest manipulation potential always belongs to plurality or to Borda Count, whether there are more voters or more candidates.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - encoding: F^s ∉ {PL, BC} → s ≠ (1, 0, …, 0) and s ≠ the normalized Borda vector; reason: the proof (p.17) argues on the vectors ('meaning F^s = BC'); a normalized scoring vector determines its rule
--   - encoding: 2/s₂ in n ≥ max(8, 2/s₂ + 4) → the real 2/s₂; reason: under 1 = s₁ ≥ … ≥ s_m = 0, s₂ = 0 forces s = (1, 0, …, 0), excluded; so s₂ > 0 and Lean's 2/0 never arises (proved in the verification file)
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.9, p.17

import Mathlib
import Definitions.Def_ManipPotential_Supplement_IsScoringVector
import Definitions.Def_ManipPotential_Supplement_scoreAt
import Definitions.Def_ManipPotential_Supplement_plurality
import Definitions.Def_ManipPotential_Supplement_borda
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

namespace ManipPotential.Supplement

/-- Theorem 4.9 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.17): for any positional scoring rule `F^s ∉ {PL, BC}`, given some
`n ≥ 4` that is divisible by `4`, either `MP(F^s) > MP(BC)` or `MP(F^s) ≥ MP(PL)`; further, if
`n ≥ max(8, 2/s₂ + 4)`, then either `MP(F^s) > MP(BC)` or `MP(F^s) > MP(PL)`.

**Formalization Note** `m ≥ 3` is Section 2's standing assumption; all three manipulation potentials
are at the same `n` and `m`. "`F^s ∉ {PL, BC}`" is `s ≠ (1, 0, …, 0)` and `s ≠` the normalized Borda
vector (the proof argues on the vectors). Under `IsScoringVector s` and `s ≠ (1, 0, …, 0)`, `s₂ > 0`,
so `2/s₂` is the real number of the page (Lean's `2/0` never arises). -/
theorem theorem_4_9 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (s : Fin m → ℝ)
    (hs : IsScoringVector s) (hPL : s ≠ pluralityVec m) (hBC : s ≠ bordaVec m)
    (hn4 : 4 ≤ n) (h4 : 4 ∣ n) :
    (manipPotentialSCCAt (borda (m := m)) n < manipPotentialSCCAt (scoringRule s) n ∨
      manipPotentialSCCAt (plurality (m := m)) n ≤ manipPotentialSCCAt (scoringRule s) n) ∧
    (max 8 (2 / scoreAt s 2 + 4) ≤ (n : ℝ) →
      (manipPotentialSCCAt (borda (m := m)) n < manipPotentialSCCAt (scoringRule s) n ∨
        manipPotentialSCCAt (plurality (m := m)) n < manipPotentialSCCAt (scoringRule s) n)) := by sorry

end ManipPotential.Supplement
