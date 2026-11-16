-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_theorem_6_9
-- name    : ListReplicableBias.LowerBound.Supplement.theorem_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:27.887445+00:00
-- url     : https://prove2.me/theorems/cde03b6e-14a6-49c0-913b-73c0c7b484ed
-- title:
--   Theorem 6.9 — Algorithm 1: Pr(⊥) ≤ 1/4, Pr(Y ∉ L_p ∪ {⊥}) ≤ η, E[N] ≤ M
-- statement:
--   Run Algorithm 1 with parameters $\varepsilon\in(0,1)$, $\eta\in(0,1/8)$ on $d\ge1$ coins with biases $p\in[0,1]^d$; let $Y$ be its output, $N$ its number of tosses and $\mathcal L_p$ the canonical list. Then
--   $$\Pr(Y=\bot)\le\frac14,\qquad\Pr\big(Y\notin\mathcal L_p\cup\{\bot\}\big)\le\eta,\qquad \mathbb E[N]\le M=\frac{1536d^2}{\varepsilon^2}\ln\frac{2dm}{\eta},$$
--   and $M=O\big(\frac{d^2}{\varepsilon^2}\log\frac d\eta\big)$ with an absolute constant.
--
--   Algorithm 1 is thus a $(d+1,\varepsilon,O(\eta))$-list replicable procedure with $\tilde O(d^2/\varepsilon^2)$ expected samples; Theorems A.1 and A.2 turn it into the fixed-budget algorithm of Theorem 6.8.
--
--   Differences from the source:
--   - encoding: Algorithm 1 run on d coins with shift U ~ Unif([0, ε)), probabilities over U and the tosses → the explicit outcome space (U, all block tosses) with law Unif([0, ε)) ⊗ independent Bern(p_i) tosses; rounds 1..m are blocks Fin m (block b is round b+1); probabilities are ℝ≥0∞ masses; reason: this is the paper's own analysis model on PDF p. 10 (an independent block of n_j tosses for every coin and round, only used blocks counted)
--   - encoding: d ∈ ℕ coins indexed by [d] → 1 ≤ d; reason: at d = 0 the parameter m = ⌈log₂(24d)⌉ (and log(d/·)) is undefined, so only undefined cases are excluded
--   - encoding: E[N] → the lower Lebesgue integral of the toss count (as ℝ≥0∞) under the outcome law, bounded by ENNReal.ofReal M; reason: N is a nonnegative toss count, so this is its expectation; it needs no integrability side condition
--   - reading: M = O((d²/ε²) log(d/η)) as an asymptotic statement → one constant chosen before every other parameter; reason: the O-constant is absolute; one constant chosen before d, ε, η is the stronger, standard reading
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem 6.9, PDF p. 9

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Algorithms

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Theorem 6.9, PDF p. 9: the properties of Algorithm 1, all four. -/
theorem theorem_6_9 :
    (∀ (d : ℕ), 1 ≤ d → ∀ ε η : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → η ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      ∀ p ∈ cube d 0 1,
        alg1Law d ε η p {ω | alg1Output ω = none} ≤ ENNReal.ofReal (1 / 4) ∧
        alg1Law d ε η p {ω | alg1Output ω ∉ (some '' canonicalList ε p) ∪ {none}} ≤
          ENNReal.ofReal η ∧
        ∫⁻ ω, (alg1Tosses ω : ℝ≥0∞) ∂(alg1Law d ε η p) ≤
          ENNReal.ofReal (expectedBound d ε η)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ ε η : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      η ∈ Set.Ioo (0 : ℝ) (1 / 8) →
        expectedBound d ε η ≤ C * (d : ℝ) ^ 2 / ε ^ 2 * Real.log ((d : ℝ) / η)) := by sorry

end ListReplicableBias.LowerBound.Supplement
