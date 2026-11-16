-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_10
-- name    : MetricMatchingDistortion.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:07:06.58161+00:00
-- url     : https://prove2.me/theorems/cbe31bbe-ae80-4d92-93f2-9d3b2782895d
-- title:
--   Theorem 10 — TruncatedPS with doubling has distortion $\Omega(n/\sqrt{\log n})$
-- statement:
--   There is a constant $c>0$ such that for arbitrarily large $n$ there exist an instance $\sigma$ with $n$ agents and a pseudometric $d$ consistent with $\sigma$ with $\mathrm{OPT}>0$ such that every output $Y$ Algorithm 8 may return on $\sigma$ satisfies
--   $$\mathrm{cost}(Y,d)\ \ge\ c\,\frac{n}{\sqrt{\log n}}\ \mathrm{OPT}.$$
--   Hence $\mathrm{distortion}(\mathrm{TruncPS},\sigma)=\Omega(n/\sqrt{\log n})$ on these instances, whatever admissible $Y$ the algorithm returns.
--
--   Together with Theorem 3 this shows that the linear bound for TruncatedPS is tight up to a $\sqrt{\log n}$ factor.
--
--   Differences from the source:
--   - reading: Ω(n/√(log n)) for arbitrarily large n → ∃ c > 0, ∀ N, ∃ n ≥ N with an n-agent instance whose ratio is at least c · n/√(log n); reason: the constant comes first and n is unbounded; the paper's construction exists only for some n (e.g. n = 2H for PS), so the claim is not for all large n
--   - reading: distortion(M, σ) ≥ L, with distortion the supremum over d ∈ ρ(σ) of E[cost]/min cost (footnote 10: 0/0 = 1, c/0 = +∞) → one pseudometric d consistent with σ with 0 < OPT = min_π cost(π, d) and E[cost] ≥ L · OPT; reason: such a d bounds the supremum from below; requiring OPT > 0 excludes the vacuous case OPT = 0, and every lower-bound instance of the paper has a positive optimum
--   - encoding: E_{M∼TruncPS(σ)}[cost(M, d)] with Y read as a lottery with marginals Y → fracCost Y d for every Y with IsTruncPSOutput rk Y (bistochastic, Y ≤ 2·X(1 − 1/(2n)) entrywise); reason: Algorithm 8 may return any such Y and the cost of a lottery with marginals Y is cost(Y, d); the bound is stated for every admissible Y
--   - encoding: n ≥ 1 (standing assumption, §2 p.9) → [NeZero n] (required by the published psAlloc); reason: the same condition as a type class
--   - encoding: log n → Real.log n (natural logarithm); reason: the base changes only the constant c
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 10, p.64 (PDF p.66)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_Supplement_optCost
import Definitions.Def_MetricMatchingDistortion_Supplement_IsTruncPSOutput

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 10 (TruncatedPS lower bound).** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 10, p.64 (PDF p.66): "For
arbitrarily large n, there exists an instance σ such that distortion(TruncPS, σ) = Ω(n/√(log(n))),
where TruncPS refers to the mechanism described in Algorithm 8."

There is a constant `c > 0` such that for every `N` there are `n ≥ N` (with `n ≥ 1`), a ranking
profile `rk` and a consistent pseudometric `d` with positive optimum `OPT` such that every output
`Y` Algorithm 8 may return satisfies `cost(Y, d) ≥ c · n/√(log n) · OPT`.

**Formalization Note.** The bound holds for every admissible `Y` (Algorithm 8 returns "any
bistochastic matrix with Y ≤ 2X(T)"); such `Y` exist by Lemma 6.14, so the quantifier is not
vacuous. A lower bound on the distortion is witnessed by one consistent `d` with `OPT > 0`. `c` is
chosen before `N`; `log` is the natural logarithm. -/
theorem theorem_10 :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, ∃ _ : NeZero n, N ≤ n ∧ ∃ rk : Ranking n,
      ∃ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d ∧
        0 < optCost d ∧ ∀ Y : Fin n → Fin n → ℝ, IsTruncPSOutput rk Y →
          c * ((n : ℝ) / Real.sqrt (Real.log n)) * optCost d ≤ fracCost Y d := by sorry

end MetricMatchingDistortion.Supplement
