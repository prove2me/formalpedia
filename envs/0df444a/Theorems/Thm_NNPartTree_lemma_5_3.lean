-- Prove2me | Theorems.Thm_NNPartTree_lemma_5_3
-- name    : NNPartTree.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:15.809902+00:00
-- url     : https://prove2.me/theorems/b19cece1-e598-4525-8315-245e91bd82aa
-- title:
--   Lemma 5.3, p.16 — uniform convergence of err and bal over degree-$k$ PTFs
-- statement:
--   There is an absolute constant $c$ such that for all $d\ge1$, $k\in\mathbb N$, $\varepsilon,\delta\in(0,1)$, every law $\mathcal D$ on pairs and every $m\ge c((d+k)^k+\log(1/\delta))/\varepsilon^2$, with probability at least $1-\delta$ over $S\sim\mathcal D^m$, every degree-$k$ polynomial threshold function $g$ satisfies
--   $$|\mathrm{err}_S(g)-\mathrm{err}_{\mathcal D}(g)|\le\varepsilon\quad\text{and}\quad|\mathrm{bal}_S(g)-\mathrm{bal}_{\mathcal D}(g)|\le\varepsilon.$$
--
--   This generalizes a cut found on a sample to the true distribution.
--
--   Differences from the source:
--   - encoding: with probability 1 − δ, m = O(…) → failure set has outer measure at most δ, for all m ≥ c(…)/ε²; d ≥ 1; reason: the failure event is an uncountable union, and no measurability is claimed; on ℝ⁰ every cut has err and bal 0
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Lemma 5.3, p.16; proof pp.46–47; Lemma A.1 and Fact A.4, p.33

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory

namespace NNPartTree

/-- **Lemma 5.3** (Uniform Convergence), p.16; proof pp.46–47. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

For `ε, δ ∈ (0, 1)` and `k ∈ ℕ`, if `m ≥ c ((d + k)^k + log(1/δ))/ε²`, then with probability `1 − δ` over `S ∼ D^m` every
`g ∈ P_k` has `|err_S(g) − err_D(g)| ≤ ε` and `|bal_S(g) − bal_D(g)| ≤ ε`.

**Formalization Note.** The failure set is an uncountable union, so its outer measure is bounded, with no measurability
claim. `c` is absolute and chosen before all binders. -/
theorem lemma_5_3 : ∃ c : ℝ, 0 < c ∧ ∀ (d k : ℕ) (ε δ : ℝ) (D : Measure (Pt d × Pt d))
    [IsProbabilityMeasure D] (m : ℕ), 1 ≤ d → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    c * (((d : ℝ) + k) ^ k + Real.log (1 / δ)) / ε ^ 2 ≤ m →
    sampleProduct D m {S | ∃ g : Pt d → ℝ, IsPTF k g ∧
        (ε < |err (empirical S) g - err D g| ∨ ε < |bal (empirical S) g - bal D g|)} ≤
      ENNReal.ofReal δ := by sorry

end NNPartTree
