-- Prove2me | Theorems.Thm_NNPartTree_lemma_6_2
-- name    : NNPartTree.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:17.277885+00:00
-- url     : https://prove2.me/theorems/81e48a04-5fad-40da-987b-06e0da1050e2
-- title:
--   Lemma 6.2, p.24 — TestMass (Large iff $\hat\mu>1.5\gamma$) on $O(\log(1/\delta)/\gamma)$ samples
-- statement:
--   There is an absolute constant $c$ such that for every probability law $Y$ on $\mathbb R^d$, measurable $W$, $\gamma,\delta\in(0,1)$ and $m\ge1$ with $m\ge c\log(1/\delta)/\gamma$, the following hold for $m$ independent samples of $Y$, with $\hat\mu$ the fraction of samples in $W$:
--
--   1. if $Y(W)\le\gamma$ then $\Pr[\hat\mu>1.5\gamma]\le\delta$, so TestMass outputs Small with probability at least $1-\delta$;
--   2. if $Y(W)\ge2\gamma$ then $\Pr[\hat\mu\le1.5\gamma]\le\delta$, so TestMass outputs Large with probability at least $1-\delta$.
--
--   Differences from the source:
--   - generalization: D_nn and W = R_T(u) → any probability law and any measurable W; reason: the proof uses neither restriction, and the printed case is an instance
--   - encoding: there exists an algorithm TestMass using O(log(1/δ)/γ) samples, evaluating membership by walking down T → the rule of the proof, on any m ≥ max(1, c log(1/δ)/γ) samples; reason: the number of samples is m, and membership in W is the walk
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Lemma 6.2, p.24; proof pp.47–48

import Mathlib
import Definitions.Def_NNPartTree_GreedyTree

open MeasureTheory

namespace NNPartTree

/-- **Lemma 6.2** (Marginal Mass Tester), p.24; proof pp.47–48. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

TestMass, the proof's rule "Large iff `μ̂ > 1.5 γ`", on `m ≥ c log(1/δ)/γ` samples, `m ≥ 1`: if the mass of `W` is at most `γ` it
outputs Small, and if the mass is at least `2γ` it outputs Large, each with probability at least `1 − δ`.

**Formalization Note.** The number of samples is `m`. Membership in `W` stands for "evaluates whether `p ∈ P^u` by walking
down `T`". `W` is any measurable set and the law any probability measure, of which `R_T(u)` and `D_nn` are cases. -/
theorem lemma_6_2 : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (Y : Measure (Pt d)) [IsProbabilityMeasure Y]
    (W : Set (Pt d)) (γ δ : ℝ) (m : ℕ), MeasurableSet W → 0 < γ → γ < 1 → 0 < δ → δ < 1 → 1 ≤ m →
    c * Real.log (1 / δ) / γ ≤ m →
    (Y W ≤ ENNReal.ofReal γ →
      (Measure.pi fun _ : Fin m => Y) {s | TestLarge γ W s} ≤ ENNReal.ofReal δ) ∧
    (ENNReal.ofReal (2 * γ) ≤ Y W →
      (Measure.pi fun _ : Fin m => Y) {s | ¬ TestLarge γ W s} ≤ ENNReal.ofReal δ) := by sorry

end NNPartTree
