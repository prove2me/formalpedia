-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_theorem_A_2
-- name    : ListReplicableBias.LowerBound.Supplement.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:23.947674+00:00
-- url     : https://prove2.me/theorems/6b1d2b48-f034-42d3-bfd1-befda251b315
-- title:
--   Theorem A.2 — Algorithm 3 is (d+1, ε, δ)-list replicable with list L_p and N ≤ BT
-- statement:
--   Run Algorithm 3 ($T=\lceil\log_2(2/\delta)\rceil$ independent runs of Algorithm 2 with $\eta=\delta/4$, returning the first non-$\bot$ output) with $\varepsilon\in(0,1)$, $\delta\in(0,1/2)$ on $d\ge1$ coins with biases $p\in[0,1]^d$; let $Y$ be its output and $N$ its number of tosses. Then
--   1. $\Pr(Y\in\mathcal L_p)\ge1-\delta$, where $\mathcal L_p=\{R_u(p):u\in[0,\varepsilon)\}$;
--   2. $|\mathcal L_p|\le d+1$;
--   3. every $y\in\mathcal L_p$ satisfies $\|y-p\|_\infty<\varepsilon$;
--   4. $N\le BT$ for every outcome;
--   5. $BT=O\big(\frac{d^2}{\varepsilon^2}\log\frac d\delta\log\frac1\delta\big)$ with an absolute constant.
--
--   This is the fixed-budget $(d+1,\varepsilon,\delta)$-list replicable algorithm behind Theorem 6.8.
--
--   Differences from the source:
--   - encoding: Algorithm 1 run on d coins with shift U ~ Unif([0, ε)), probabilities over U and the tosses → the explicit outcome space (U, all block tosses) with law Unif([0, ε)) ⊗ independent Bern(p_i) tosses; rounds 1..m are blocks Fin m (block b is round b+1); probabilities are ℝ≥0∞ masses; reason: this is the paper's own analysis model on PDF p. 10 (an independent block of n_j tosses for every coin and round, only used blocks counted)
--   - encoding: d ∈ ℕ coins indexed by [d] → 1 ≤ d; reason: at d = 0 the parameter m = ⌈log₂(24d)⌉ (and log(d/·)) is undefined, so only undefined cases are excluded
--   - encoding: T independent instances of Algorithm 2 → the product of T copies of Algorithm 2's outcome law (with η = δ/4); toss count summed over runs 1..K, or all T runs; reason: the paper's proof imagines generating all T independent instances
--   - encoding: Pr(Y ∈ L_p) ≥ 1 − δ and |L_p| ≤ d + 1 → ENNReal.ofReal (1 − δ) ≤ the mass of {Y ∈ some '' L_p}, with ⊥ outside; Set.encard L_p ≤ d + 1; reason: ⊥ is not a list member; encard also asserts finiteness
--   - reading: BT = O((d²/ε²) log(d/δ) log(1/δ)) asymptotically → one constant C chosen before d, ε, δ, valid for all δ ∈ (0, 1/2); reason: the O-constant is absolute; the uniform reading is the stronger one
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem A.2, PDF p. 14

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Algorithms

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Theorem A.2, PDF p. 14: Algorithm 3 is (d+1, ε, δ)-list replicable with list
L_p, all five conclusions; ⊥ counts as outside the list. -/
theorem theorem_A_2 :
    (∀ (d : ℕ), 1 ≤ d → ∀ ε δ : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (1 / 2) →
      ∀ p ∈ cube d 0 1,
        ENNReal.ofReal (1 - δ) ≤ alg3Law d ε δ p {ω | alg3Output ω ∈ some '' canonicalList ε p} ∧
        (canonicalList ε p).encard ≤ (d : ℕ∞) + 1 ∧
        (∀ y ∈ canonicalList ε p, ‖y - p‖ < ε) ∧
        ∀ ω : Outcome3 d ε δ, alg3Tosses ω ≤ sampleCap d ε (δ / 4) * numAttempts δ) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ ε δ : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      δ ∈ Set.Ioo (0 : ℝ) (1 / 2) →
        ((sampleCap d ε (δ / 4) * numAttempts δ : ℕ) : ℝ) ≤
          C * (d : ℝ) ^ 2 / ε ^ 2 * Real.log ((d : ℝ) / δ) * Real.log (1 / δ)) := by sorry

end ListReplicableBias.LowerBound.Supplement
