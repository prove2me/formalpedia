-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_theorem_A_1
-- name    : ListReplicableBias.LowerBound.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:30:47.929737+00:00
-- url     : https://prove2.me/theorems/568430c7-1623-4f1b-8a6f-7f0d746b0f90
-- title:
--   Theorem A.1 — Algorithm 2 (capped at B = ⌈4M⌉): Pr(⊥) ≤ 1/2, Pr(Y ∉ L_p ∪ {⊥}) ≤ η, N ≤ B
-- statement:
--   Run Algorithm 2 (Algorithm 1 capped at $B=\lceil4M\rceil$ tosses) with parameters $\varepsilon\in(0,1)$, $\eta\in(0,1/8)$ on $d\ge1$ coins with biases $p\in[0,1]^d$; let $Y$ be its output and $N$ its number of tosses. Then
--   $$\Pr(Y=\bot)\le\frac12,\qquad\Pr\big(Y\notin\mathcal L_p\cup\{\bot\}\big)\le\eta,\qquad N\le B=\lceil4M\rceil\ \text{always},$$
--   and $B=O\big(\frac{d^2}{\varepsilon^2}\log\frac d\eta\big)$ with an absolute constant.
--
--   Capping converts the expected sample bound of Theorem 6.9 into a worst-case one at the price of a larger failure probability.
--
--   Differences from the source:
--   - encoding: Algorithm 1 run on d coins with shift U ~ Unif([0, ε)), probabilities over U and the tosses → the explicit outcome space (U, all block tosses) with law Unif([0, ε)) ⊗ independent Bern(p_i) tosses; rounds 1..m are blocks Fin m (block b is round b+1); probabilities are ℝ≥0∞ masses; reason: this is the paper's own analysis model on PDF p. 10 (an independent block of n_j tosses for every coin and round, only used blocks counted)
--   - encoding: d ∈ ℕ coins indexed by [d] → 1 ≤ d; reason: at d = 0 the parameter m = ⌈log₂(24d)⌉ (and log(d/·)) is undefined, so only undefined cases are excluded
--   - encoding: Algorithm 2 runs Algorithm 1 with a cap of B samples → on the same outcome: output none if Algorithm 1's toss count exceeds B, else Algorithm 1's output; toss count min(N₁, B), bounded for every outcome; reason: the paper's proof runs both algorithms with the same shift and samples
--   - reading: M = O((d²/ε²) log(d/η)) as an asymptotic statement → one constant chosen before every other parameter; reason: the O-constant is absolute; one constant chosen before d, ε, η is the stronger, standard reading
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem A.1, PDF p. 13

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Algorithms

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Theorem A.1, PDF p. 13: the properties of Algorithm 2, all four. The toss
bound holds for every outcome (worst case). -/
theorem theorem_A_1 :
    (∀ (d : ℕ), 1 ≤ d → ∀ ε η : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → η ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      ∀ p ∈ cube d 0 1,
        alg1Law d ε η p {ω | alg2Output ω = none} ≤ ENNReal.ofReal (1 / 2) ∧
        alg1Law d ε η p {ω | alg2Output ω ∉ (some '' canonicalList ε p) ∪ {none}} ≤
          ENNReal.ofReal η ∧
        ∀ ω : Outcome1 d ε η, alg2Tosses ω ≤ sampleCap d ε η) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ ε η : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      η ∈ Set.Ioo (0 : ℝ) (1 / 8) →
        (sampleCap d ε η : ℝ) ≤ C * (d : ℝ) ^ 2 / ε ^ 2 * Real.log ((d : ℝ) / η)) := by sorry

end ListReplicableBias.LowerBound.Supplement
