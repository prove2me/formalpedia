-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_6
-- name    : MetricMatchingDistortion.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:07:51.030425+00:00
-- url     : https://prove2.me/theorems/6169e784-eecc-486d-a3ab-abf9952c77d2
-- title:
--   Theorem 6 — truthful-in-expectation mechanisms have distortion $2^{\Omega(\sqrt{\log n})}$
-- statement:
--   There is a universal constant $c>0$ such that for every truthful-in-expectation matching mechanism $M$ and arbitrarily large $n$ there exist an instance $\sigma$ with $n$ agents and a pseudometric $d$ consistent with $\sigma$ with $\mathrm{OPT}>0$ and
--   $$\mathbb E_{M'\sim M(\sigma)}[\mathrm{cost}(M',d)]\ \ge\ 2^{c\sqrt{\log n}}\ \mathrm{OPT}.$$
--   Hence every truthful-in-expectation mechanism has distortion at least $2^{\Omega(\sqrt{\log n})}$.
--
--   This is the first lower bound for truthful mechanisms beyond the $\Omega(\log n)$ bound that holds for all mechanisms.
--
--   Differences from the source:
--   - reading: distortion at least 2^{Ω(√log n)} → ∃ c > 0 chosen before the mechanism; for every truthful-in-expectation M and every N, ∃ n ≥ N with an n-agent instance whose ratio is at least 2^{c√(log n)}; reason: Ω gives one universal constant; the proof (p.67) builds instances only for n = Σ_{t≤k} r^t, so the bound is for arbitrarily large n
--   - reading: distortion(M, σ) ≥ L, with distortion the supremum over d ∈ ρ(σ) of E[cost]/min cost (footnote 10: 0/0 = 1, c/0 = +∞) → one pseudometric d consistent with σ with 0 < OPT = min_π cost(π, d) and E[cost] ≥ L · OPT; reason: such a d bounds the supremum from below; requiring OPT > 0 excludes the vacuous case OPT = 0, and every lower-bound instance of the paper has a positive optimum
--   - encoding: truthful-in-expectation (Definition 2.1) → IsTruthfulInExpectation: inequality (1) for every n, every rk, rk' differing only in agent a's ranking, every d consistent with rk; reason: Definition 2.1 verbatim; not assumed anonymous or Pareto optimal
--   - encoding: log n → Real.log n (natural logarithm); reason: the base changes only the constant c
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 6, p.65 (PDF p.67)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_Mechanism
import Definitions.Def_MetricMatchingDistortion_Supplement_optCost
import Definitions.Def_MetricMatchingDistortion_Supplement_Truthful

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 6 (truthful mechanisms).** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 6, p.65 (PDF p.67): "Every
truthful-in-expectation matching mechanism has distortion at least 2^{Ω(√log n)}."

There is a universal constant `c > 0` such that for every truthful-in-expectation mechanism `A`
(Definition 2.1) and every `N` there are `n ≥ N`, a ranking profile `rk` on `n` agents and items and
a consistent pseudometric `d` with positive optimum `OPT` and
`E_{M∼A(rk)}[cost(M, d)] ≥ 2^{c √(log n)} · OPT`.

**Formalization Note.** `c` is chosen before the mechanism. `2^{Ω(√log n)}` is read "for
arbitrarily large n" (the proof, p.67, builds instances with `n = ∑_{t ≤ k} r^t`, `r = k2^{k+1}`,
for every `k`). A lower bound on the distortion is witnessed by one consistent `d` with `OPT > 0`.
The mechanism is not assumed anonymous or Pareto optimal. `log` is the natural logarithm. -/
theorem theorem_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Mechanism, IsTruthfulInExpectation A →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ rk : Ranking n,
        ∃ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d ∧
          0 < optCost d ∧
          (2 : ℝ) ^ (c * Real.sqrt (Real.log n)) * optCost d ≤ expectedCost A n rk d := by sorry

end MetricMatchingDistortion.Supplement
