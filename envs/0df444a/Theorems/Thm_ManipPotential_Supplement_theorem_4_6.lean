-- Prove2me | Theorems.Thm_ManipPotential_Supplement_theorem_4_6
-- name    : ManipPotential.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:12:52.089534+00:00
-- url     : https://prove2.me/theorems/b4aa2898-848a-4cd2-83a1-4c0486305ed3
-- title:
--   Theorem 4.6 — $\mathrm{MP}(F^s) \le \max_{\ell} U_s(\ell)$ when $s_1 \ne s_2$
-- statement:
--   Let $m \ge 3$, $n \ge 2$, and let $s$ be a positional scoring vector with $s_1 \ne s_2$. Then
--   $$\mathrm{MP}(F^s) \le \max_{\ell \in [m-1]} U_s(\ell),$$
--   where $U_s(1) = \frac{1}{s_1 - s_2} - 1$ and, for $\ell \ge 2$,
--   $$U_s(\ell) = \min\left( \frac{1}{s_\ell - s_{\ell+1}} - 1,\ \frac{(n-1)\bigl(\overline{s}(2) - \underline{s}(\alpha^s_\ell)\bigr) + \frac12}{\overline{s}(\alpha^s_\ell) - s_{\ell+1}} \right),$$
--   with $\overline s$, $\underline s$ the top and bottom averages, $\alpha^s_\ell = \max\{\ell' \in [\ell-1] : s_{\ell'} > s_{\ell+1}\}$, and $\frac{1}{s_\ell - s_{\ell+1}} = \infty$ when $s_\ell = s_{\ell+1}$.
--
--   As in the paper (Section 4, p.10; proof in Appendix A.1), the upper bound means: $F^s$ is $k$-ASP for every integer $k \ge \max_{\ell \in [m-1]} U_s(\ell)$, i.e. $\mathrm{MP}(F^s) \le \lceil \max_\ell U_s(\ell) \rceil$.
--
--   The bound is finite, so together with Theorem 4.5 the condition $s_1 = s_2$ is necessary and sufficient for an unbounded manipulation potential. For plurality and Borda Count it gives $n/2$ and $m-2$.
--
--   Differences from the source:
--   - encoding: profiles ≻_N ∈ L(C)^n, rankings as relations, winner sets in P(C), MP ∈ ℤ_{≥0} ∪ {∞} → List (Ranking m) of length n with rankings as permutations to 0-based positions, Finset (Fin m), MP in ℕ∞; reason: Lean convention; same instances
--   - encoding: F_T(≻_N) = top_T F(≻_N), defined for nonempty F(≻_N) → tieBreak F T, equal to top_T C when F(≻_N) = ∅; reason: the rules of this theorem return a nonempty winner set on every profile, so no instance changes
--   - reading: MP(F^s) ≤ max_ℓ U_s(ℓ), an integer-or-∞ quantity bounded by a real number → F^s is k-ASP for every integer k ≥ max_ℓ U_s(ℓ) (MP(F^s) ≤ ⌈max_ℓ U_s(ℓ)⌉); reason: the paper's convention for upper bounds (Section 4, 'Proof Structure', p.10: MP(F) ≤ k means k'-ASP for all k' ≥ k), the proof in Appendix A.1 ('fix … some k ≥ max U_s(ℓ)'), and p.16: the bound n/2 recovers Theorem 4.2 'with a minor loss for PL if n is odd', which is a loss only under this reading
--   - encoding: the real U_s(ℓ) with 1/(s_ℓ − s_{ℓ+1}) = ∞ when s_ℓ = s_{ℓ+1} → U_s(ℓ) in EReal with ⊤ for s_ℓ = s_{ℓ+1}, the max a supremum over Finset.Icc 1 (m − 1), compared with the cast of k; reason: Lean convention; the same comparison
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Theorem 4.6, pp.15–16 (restated in Appendix A.1, p.48)

import Mathlib
import Definitions.Def_ManipPotential_Supplement_IsScoringVector
import Definitions.Def_ManipPotential_Supplement_scoringRule
import Definitions.Def_ManipPotential_Supplement_upperBoundU
import Definitions.Def_ManipPotential_Supplement_IsKASPAtSCC

open scoped ENNReal

namespace ManipPotential.Supplement

/-- Theorem 4.6 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), p.15; restated in Appendix A.1, p.48): for any `F^s` with `s₁ ≠ s₂`,
`MP(F^s) ≤ max_{ℓ∈[m−1]} U_s(ℓ)`, with `U_s(ℓ)` as in `upperBoundU`.

**Formalization Note** `m ≥ 3` and `n ≥ 2` are Section 2's standing assumptions (p.7); `k`-ASP is
at the fixed electorate size `n` (`IsKASPAtSCC`: for all of the `m!` tiebreakers). The upper bound
`MP(F^s) ≤ x` for a real `x` is stated in the paper's own sense: `F^s` is `k`-ASP for every integer
`k ≥ x` (Section 4, "Proof Structure", p.10: an upper bound `MP(F) ≤ k` means `k'`-ASP for all
`k' ≥ k`; the proof in Appendix A.1 fixes "some `k ≥ max_ℓ U_s(ℓ)`"), equivalently
`MP(F^s) ≤ ⌈max_ℓ U_s(ℓ)⌉`. The paper confirms this reading on p.16: for plurality the bound is
`n/2`, which recovers Theorem 4.2 "with a minor loss for PL if `n` is odd" (a loss only under the
ceiling reading). `max_ℓ U_s(ℓ)` is an `EReal` supremum over `ℓ ∈ Finset.Icc 1 (m − 1)`. -/
theorem theorem_4_6 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (n : ℕ) (hn : 2 ≤ n) (s : Fin m → ℝ) (hs : IsScoringVector s)
    (h12 : scoreAt s 1 ≠ scoreAt s 2) :
    ∀ k : ℕ, (⨆ ℓ ∈ Finset.Icc 1 (m - 1), upperBoundU s n ℓ) ≤ ((k : ℝ) : EReal) →
      IsKASPAtSCC (scoringRule s) n k := by sorry

end ManipPotential.Supplement
