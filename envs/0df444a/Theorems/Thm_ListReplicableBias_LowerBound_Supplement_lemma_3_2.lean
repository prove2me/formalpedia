-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_3_2
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:23:52.798182+00:00
-- url     : https://prove2.me/theorems/24465e3f-40ea-4e54-a277-c3b0eef4ccdc
-- title:
--   Lemma 3.2 — Ω(d/ε²) samples for coin-bias estimation
-- statement:
--   There is an absolute constant $c>0$ such that for every $d\in\mathbb N$, every $\varepsilon,\delta\in(0,1/8)$, and every randomized adaptive $N$-toss sampling algorithm $A$ that solves the $(d,\varepsilon,\delta)$-CoinBiasEstimationProblem,
--   $$N\ge c\,\frac{d}{\varepsilon^2}.$$
--
--   The constant does not depend on $d,\varepsilon,\delta,N$ or $A$. The paper cites this classical bound ([KCG16, Sca24]); the proof of Theorem 5.11 uses it for list sizes $k>\tfrac12e^{d/20}$.
--
--   Differences from the source:
--   - encoding: arbitrary randomized adaptive algorithms with sample access to d coins, using N samples, output in ℝ^d ∪ {⊥} → the published SamplingAlgorithm d N (arbitrary probability seed space, prefix-dependent coin choices, fixed horizon N) with failure as none; reason: the base mission's model of §3.2 and Appendix B; private randomness is in the seed and an algorithm that stops early is padded with ignored tosses, so N is the worst-case toss count
--   - reading: N = Ω(d/ε²) with ε, δ fixed first → one constant chosen before every other parameter; reason: the hidden constant cannot depend on ε, which appears inside the bound; the uniform reading is the stronger one
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 3.2, PDF p. 3

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Estimation

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 3.2, PDF p. 3. One absolute constant c, chosen before d, ε, δ, N and A. -/
theorem lemma_3_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, ∀ ε δ : ℝ, ε ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      δ ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      ∀ (N : ℕ) (A : SamplingAlgorithm d N), IsBiasEstimator A ε δ →
        c * (d : ℝ) / ε ^ 2 ≤ (N : ℝ) := by sorry

end ListReplicableBias.LowerBound.Supplement
