-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_11
-- name    : ManipPotential.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:15:30.503356+00:00
-- url     : https://prove2.me/theorems/7429f958-dfe0-49ec-b6de-6506061243e2
-- title:
--   Theorem 4.11 — bounds on $\mathrm{MP}(\mathrm{MM})$
-- statement:
--   Let $m \ge 3$ candidates and $n \ge 2$ voters.
--
--   1. (Upper bound.) $\mathrm{MP}(\mathrm{MM}) \le \dfrac{(m-2)n}{m-1} + 2$, in the paper's sense: Maximin is $k$-ASP for every integer $k \ge \frac{(m-2)n}{m-1} + 2$.
--   2. (Lower bound.) If $n - 2$ is divisible by $m - 1$, then
--   $$\mathrm{MP}(\mathrm{MM}) \ge \frac{(m-2)(n-2)}{m-1} + 1,$$
--   and Maximin is not $k$-ASP for any $k < \frac{(m-2)(n-2)}{m-1} + 1$.
--
--   So the manipulation potential of Maximin depends on both $m$ and $n$, growing like $\frac{m-2}{m-1}\,n$.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - reading: '(assuming n − 2 is divisible by m − 1) at least …', then 'Further, MM is not k-ASP for any k < (m−2)(n−2)/(m−1) + 1' → divisibility on the lower bound and on the 'not k-ASP' clause; the upper bound at every n ≥ 2; reason: Proposition A.2 (p.52) states the divisibility assumption for both the lower bound and the 'not k-ASP' sentence; Proposition A.1 has none
--   - reading: MP(MM) at most the real (m−2)n/(m−1) + 2 → MM is k-ASP for every integer k ≥ (m−2)n/(m−1) + 2 (MP(MM) ≤ ⌈(m−2)n/(m−1) + 2⌉); reason: the paper's convention for upper bounds (Section 4, 'Proof Structure', p.10) and Proposition A.1 (p.51), whose proof fixes 'integer k ≥ (m−2)n/(m−1) + 2'; the same convention makes Theorem 4.6's bound n/2 give Theorem 4.2 'with a minor loss for PL if n is odd' (p.16)
--   - encoding: the real lower bound compared with MP → MP cast to ℝ≥0∞, bound as ENNReal.ofReal; reason: the bound is nonnegative for m ≥ 3 and n ≥ 2, so the comparison is the same
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.11, p.20 (restated in Appendix A.4, p.51, as Propositions A.1 and A.2)

import Mathlib
import Definitions.Def_ManipPotential_Supplement_maximin
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC
import Definitions.Def_ManipPotential_Supplement_manipPotentialSCCAt

open scoped ENNReal

namespace ManipPotential.Supplement

/-- Theorem 4.11 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.20; restated in Appendix A.4, p.51, as Propositions A.1 and A.2): the
manipulation potential of Maximin is at most `(m−2)n/(m−1) + 2` and (assuming `n − 2` is divisible
by `m − 1`) at least `(m−2)(n−2)/(m−1) + 1`; further, `MM` is not `k`-ASP for any
`k < (m−2)(n−2)/(m−1) + 1`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `MP` and `k`-ASP are at the fixed electorate size `n` (`manipPotentialSCCAt`, `IsKASPAtSCC`: maximum, resp. for all, over the `m!` tiebreakers). The upper bound "at most `x`" for the real
`x = (m−2)n/(m−1) + 2` is stated in the paper's own sense: Maximin is `k`-ASP for every integer
`k ≥ x` (Section 4, "Proof Structure", p.10; Proposition A.1, p.51, fixes "integer `k ≥ x`"),
equivalently `MP(MM) ≤ ⌈x⌉`. The lower bound is compared with `MP` in `ℝ≥0∞` (it is
nonnegative, so `ENNReal.ofReal` is exact). The divisibility assumption covers the lower bound and
the "not `k`-ASP" clause, as in Proposition A.2 (p.52). -/
theorem theorem_4_11 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) :
    (∀ k : ℕ, ((m : ℝ) - 2) * n / ((m : ℝ) - 1) + 2 ≤ (k : ℝ) →
      IsKASPAtSCC (maximin (m := m)) n k) ∧
    ((m - 1) ∣ (n - 2) →
      ENNReal.ofReal (((m : ℝ) - 2) * ((n : ℝ) - 2) / ((m : ℝ) - 1) + 1) ≤
        ((manipPotentialSCCAt (maximin (m := m)) n : ℕ∞) : ℝ≥0∞) ∧
      ∀ k : ℕ, (k : ℝ) < ((m : ℝ) - 2) * ((n : ℝ) - 2) / ((m : ℝ) - 1) + 1 →
        ¬ IsKASPAtSCC (maximin (m := m)) n k) := by sorry

end ManipPotential.Supplement
