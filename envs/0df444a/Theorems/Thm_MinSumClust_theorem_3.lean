-- Prove2me | Theorems.Thm_MinSumClust_theorem_3
-- name    : MinSumClust.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:30.509611+00:00
-- url     : https://prove2.me/theorems/8453f7af-8640-44bb-9938-c2125c7c137a
-- title:
--   Theorem 3 — bipoint rounding: feasible $k$-solution of expected cost $\le 108(\cdot)$ (running-time clause carried by Theorem 1)
-- statement:
--   Let $d$ be a pseudometric on a finite set $D$ and let $\mathcal S_1,\mathcal S_2$ be partitions of $D$ into $k_1$ and $k_2$ clusters with $k_1\le k<k_2$. The rounding algorithm of §5 (for $\alpha>1/2$ a split of $\mathcal S_1$ into $k$ nonempty clusters, otherwise the labelings of §5.3 and Algorithms 5–7) outputs, in every outcome, a feasible $k$-solution $\mathcal S$ (a partition of $D$ into exactly $k$ nonempty clusters), and
--
--   $$\mathbb E[\mathrm{cost}(\mathcal S)]\ \le\ 108\cdot\Bigl(\frac{k_2-k}{k_2-k_1}\cdot\mathrm{cost}(\mathcal S_1)+\frac{k-k_1}{k_2-k_1}\cdot\mathrm{cost}(\mathcal S_2)\Bigr).$$
--
--   This holds for every split of $\mathcal S_1$ into $k$ parts and every tie-breaking order of Algorithm 6. With Theorem 2 and the binary search of Appendix A.1 it gives Theorem 1, with $2.16\times10^9=108\times2\times10^7$.
--
--   Differences from the source:
--
--   - reading: there is a polynomial-time randomized algorithm that outputs a feasible k-solution of expected cost at most 108(…) → the paper's own algorithm (round), as an exact distribution, is feasible in every outcome and has expected cost at most 108(…), for every split and tie ranking; reason: a bare ∃ of a distribution would be trivial (an optimal partition); fixed-length fair coins cannot sample the uniform choices of §5 exactly and 108 has no slack, so the running time and the coin simulation are carried by Theorem 1 (paper.md decision 6)
--   - generalization: d is a metric → d is any pseudometric (distinct points may be at distance 0); reason: the argument uses only nonnegativity, symmetry, the zero diagonal and the triangle inequality; every metric is a pseudometric, so the paper's statement is the special case
--   - encoding: a feasible k-solution 𝒮 → an outcome whose final clusters, indexed by tagged opened clusters, are nonempty, pairwise disjoint, cover D and number k; partitions as Finpartition; ordered-pair cost; reason: same solutions
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Theorem 3, p.4 (PDF p.6); restated p.42 (PDF p.44); §5, pp.42–57

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_pexp
import Definitions.Def_MinSumClust_alg7
import Definitions.Def_MinSumClust_round

namespace MinSumClust

/-- **Theorem 3 (bipoint rounding)**, p.4 (PDF p.6); restated p.42 (PDF p.44).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Theorem 3, p.4, with the algorithm of §5 (pp.42–57).

Given a `k₁`-solution `𝒮₁` and a `k₂`-solution `𝒮₂` with `k₁ ≤ k < k₂`, the rounding algorithm
outputs a feasible `k`-solution `𝒮` (in every outcome) of expected cost at most
`108 · ((k₂ − k)/(k₂ − k₁) · cost(𝒮₁) + (k − k₁)/(k₂ − k₁) · cost(𝒮₂))`.

**Formalization Note.** "There is a polynomial-time randomized algorithm" is read as the paper's
own algorithm (`round`: for `α > 1/2` a split of `𝒮₁` into `k` parts, otherwise Algorithms 5–7),
as an exact distribution; the claim holds for every split `sp` refining `𝒮₁` into `k` parts and
every tie ranking `rk`. Its running time and coin simulation are carried by Theorem 1. `d` is any
pseudometric; costs count ordered pairs. -/
theorem theorem_3 {D : Type} [Fintype D] [DecidableEq D] (d : D → D → ℝ) (hd : IsPseudometric d)
    (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (k : ℕ) (hk₁ : S₁.parts.card ≤ k)
    (hk₂ : k < S₂.parts.card) (rk : Finset D → ℕ) (sp : Finpartition (Finset.univ : Finset D))
    (hsp : sp ≤ S₁) (hspk : sp.parts.card = k) :
    (∀ o ∈ (round S₁ S₂ k rk sp.parts).support, IsKOutcome o k) ∧
      pexp (round S₁ S₂ k rk sp.parts) (outCost d) ≤
        108 * (((S₂.parts.card : ℝ) - k) / ((S₂.parts.card : ℝ) - S₁.parts.card) *
              ∑ S ∈ S₁.parts, cost d S +
            ((k : ℝ) - S₁.parts.card) / ((S₂.parts.card : ℝ) - S₁.parts.card) *
              ∑ S ∈ S₂.parts, cost d S) := by sorry

end MinSumClust
