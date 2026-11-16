-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_8
-- name    : MetricMatchingDistortion.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:04:57.990409+00:00
-- url     : https://prove2.me/theorems/e0374c0d-f714-4465-9cde-b2dac7f1514f
-- title:
--   Theorem 8 — PS has distortion $\Omega((10/9)^{n/2})$
-- statement:
--   There is a constant $c>0$ such that for arbitrarily large $n$ there exist an instance $\sigma$ with $n$ agents and a pseudometric $d$ consistent with $\sigma$ with $\mathrm{OPT}>0$ and
--   $$\mathbb E_{M\sim\mathrm{PS}(\sigma)}[\mathrm{cost}(M,d)]=\mathrm{cost}(X(1),d)\ \ge\ c\,(10/9)^{n/2}\,\mathrm{OPT},$$
--   where $X(1)$ is the final fractional matching of the Probabilistic Serial rule.
--
--   So the distortion of PS can be exponential in $n$.
--
--   Differences from the source:
--   - reading: Ω((10/9)^{n/2}) for arbitrarily large n → ∃ c > 0, ∀ N, ∃ n ≥ N with an n-agent instance whose ratio is at least c · (10/9)^{n/2}; reason: the constant comes first and n is unbounded; the paper's construction exists only for some n (e.g. n = 2H for PS), so the claim is not for all large n
--   - reading: distortion(M, σ) ≥ L, with distortion the supremum over d ∈ ρ(σ) of E[cost]/min cost (footnote 10: 0/0 = 1, c/0 = +∞) → one pseudometric d consistent with σ with 0 < OPT = min_π cost(π, d) and E[cost] ≥ L · OPT; reason: such a d bounds the supremum from below; requiring OPT > 0 excludes the vacuous case OPT = 0, and every lower-bound instance of the paper has a positive optimum
--   - encoding: E_{M∼PS(σ)}[cost(M, d)] → fracCost (psAlloc rk 1) d = cost(X(1), d); reason: the page's own identity E_{M∼PS(σ)}[cost(M, d)] = cost(X(1), d) (p.46); X is the published PS trajectory psAlloc
--   - encoding: n ≥ 1 (standing assumption, §2 p.9) → [NeZero n] (required by the published psAlloc); reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 8, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_psAlloc
import Definitions.Def_MetricMatchingDistortion_Supplement_optCost

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 8 (PS lower bound).** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 8, p.46 (PDF p.48): "For arbitrarily
large n, there exists an instance σ such that distortion(PS, σ) = Ω((10/9)^{n/2})."

There is a constant `c > 0` such that for every `N` there are `n ≥ N` (with `n ≥ 1`), a ranking
profile `rk` and a consistent pseudometric `d` with positive optimum `OPT` and
`E_{M∼PS(rk)}[cost(M, d)] = cost(X(1), d) ≥ c · (10/9)^{n/2} · OPT`.

**Formalization Note.** The expected cost of PS is `cost(X(1), d)` (p.46: "E_{M∼PS(σ)}[cost(M, d)]
= cost(X(1), d)"), with `X` the base mission's PS trajectory `psAlloc`. A lower bound on the
distortion is witnessed by one consistent `d` with `OPT > 0`, which rules out the vacuous case
`OPT = 0`. `c` is chosen before `N`; `(10/9)^{n/2}` is a real power. -/
theorem theorem_8 :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, ∃ _ : NeZero n, N ≤ n ∧ ∃ rk : Ranking n,
      ∃ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d ∧
        0 < optCost d ∧
        c * (10 / 9 : ℝ) ^ ((n : ℝ) / 2) * optCost d ≤ fracCost (psAlloc rk 1) d := by sorry

end MetricMatchingDistortion.Supplement
