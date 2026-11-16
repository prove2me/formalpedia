-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_1
-- name    : MetricMatchingDistortion.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:04:28.304301+00:00
-- url     : https://prove2.me/theorems/f15c78a9-a3b4-46c9-9fa9-b0ca6c26ba2c
-- title:
--   Theorem 1 — RSD has distortion $\Omega(n/\sqrt{\log n})$
-- statement:
--   There is a constant $c>0$ such that for arbitrarily large $n$ there exist an instance $\sigma$ with $n$ agents and a pseudometric $d$ consistent with $\sigma$ with $\mathrm{OPT}=\min_\pi\mathrm{cost}(\pi,d)>0$ and
--   $$\mathbb E_{M\sim\mathrm{RSD}(\sigma)}[\mathrm{cost}(M,d)]\ \ge\ c\,\frac{n}{\sqrt{\log n}}\ \mathrm{OPT}.$$
--   Hence $\mathrm{distortion}(\mathrm{RSD},\sigma)=\Omega(n/\sqrt{\log n})$ on these instances.
--
--   Random Serial Dictatorship processes the agents in a uniformly random order and gives each her favorite available item. The theorem shows it is far from the sublinear distortion achievable by other mechanisms.
--
--   Differences from the source:
--   - reading: Ω(n/√(log n)) for arbitrarily large n → ∃ c > 0, ∀ N, ∃ n ≥ N with an n-agent instance whose ratio is at least c · n/√(log n); reason: the constant comes first and n is unbounded; the paper's construction exists only for some n (e.g. n = 2H for PS), so the claim is not for all large n
--   - reading: distortion(M, σ) ≥ L, with distortion the supremum over d ∈ ρ(σ) of E[cost]/min cost (footnote 10: 0/0 = 1, c/0 = +∞) → one pseudometric d consistent with σ with 0 < OPT = min_π cost(π, d) and E[cost] ≥ L · OPT; reason: such a d bounds the supremum from below; requiring OPT > 0 excludes the vacuous case OPT = 0, and every lower-bound instance of the paper has a positive optimum
--   - encoding: RSD → rsdExpectedCost: the average of the serial-dictatorship cost over all n! processing orders; reason: uniform random order
--   - encoding: log n → Real.log n (natural logarithm); reason: the base changes only the constant c
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 1, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_Supplement_optCost
import Definitions.Def_MetricMatchingDistortion_Supplement_RSD

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 1 (RSD lower bound).** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 1, p.27 (PDF p.29): "For arbitrarily
large n, there exists an instance σ with n agents such that distortion(RSD, σ) = Ω(n/√(log n))."

There is a constant `c > 0` such that for every `N` there are `n ≥ N`, a ranking profile `rk` on
`n` agents and items and a consistent pseudometric `d` with positive optimum `OPT = optCost d` and
`E_{M∼RSD(rk)}[cost(M, d)] ≥ c · n/√(log n) · OPT`.

**Formalization Note.** `distortion(RSD, σ) ≥ L` is witnessed by one consistent `d` with
`OPT > 0` and `E[cost] ≥ L · OPT`, which bounds the page's supremum from below; requiring `OPT > 0`
rules out the vacuous case `OPT = 0`. The constant `c` is chosen before `N`, `n`, the instance and
the metric. `log` is the natural logarithm (the base only changes `c`). RSD's expected cost is the
average over all `n!` processing orders of the serial-dictatorship cost (`rsdExpectedCost`). -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ rk : Ranking n,
      ∃ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d ∧
        0 < optCost d ∧
        c * ((n : ℝ) / Real.sqrt (Real.log n)) * optCost d ≤ rsdExpectedCost rk d := by sorry

end MetricMatchingDistortion.Supplement
