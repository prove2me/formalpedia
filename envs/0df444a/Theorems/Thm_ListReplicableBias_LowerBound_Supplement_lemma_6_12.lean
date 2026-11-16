-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_6_12
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_6_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:48.459413+00:00
-- url     : https://prove2.me/theorems/ae99e523-ee4c-4c21-8cd8-b31e5c17299d
-- title:
--   Lemma 6.12 — Algorithm 1 uses at most M = (1536d²/ε²) ln(2dm/η) tosses in expectation
-- statement:
--   In the setting of Algorithm 1 ($\varepsilon\in(0,1)$, $\eta\in(0,1/8)$, $d\ge1$, $p\in[0,1]^d$), the number $N$ of tosses Algorithm 1 uses satisfies
--   $$\mathbb E[N]\le M=\frac{1536d^2}{\varepsilon^2}\ln\frac{2dm}{\eta},\qquad m=\lceil\log_2(24d)\rceil,$$
--   and there is an absolute constant $C>0$ with $M\le C\,\frac{d^2}{\varepsilon^2}\ln\frac d\eta$ for all such $d,\varepsilon,\eta$.
--
--   This expected sample complexity is the source of the quadratic dependence on $d$ in the upper bounds; capping it (Theorem A.1) gives a worst-case bound.
--
--   Differences from the source:
--   - encoding: Algorithm 1 run on d coins with shift U ~ Unif([0, ε)), probabilities over U and the tosses → the explicit outcome space (U, all block tosses) with law Unif([0, ε)) ⊗ independent Bern(p_i) tosses; rounds 1..m are blocks Fin m (block b is round b+1); probabilities are ℝ≥0∞ masses; reason: this is the paper's own analysis model on PDF p. 10 (an independent block of n_j tosses for every coin and round, only used blocks counted)
--   - encoding: d ∈ ℕ coins indexed by [d] → 1 ≤ d; reason: at d = 0 the parameter m = ⌈log₂(24d)⌉ (and log(d/·)) is undefined, so only undefined cases are excluded
--   - encoding: E[N] → the lower Lebesgue integral of the toss count (as ℝ≥0∞) under the outcome law, bounded by ENNReal.ofReal M; reason: N is a nonnegative toss count, so this is its expectation; it needs no integrability side condition
--   - reading: M = O((d²/ε²) log(d/η)) as an asymptotic statement → one constant chosen before every other parameter; reason: the O-constant is absolute; one constant chosen before d, ε, η is the stronger, standard reading
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 6.12, PDF pp. 11

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Algorithms

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 6.12, PDF p. 11: E[N] ≤ M with the constant 1536, and the uniform
O-clause M = O((d²/ε²) log(d/η)). -/
theorem lemma_6_12 :
    (∀ (d : ℕ), 1 ≤ d → ∀ ε η : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → η ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      ∀ p ∈ cube d 0 1,
        ∫⁻ ω, (alg1Tosses ω : ℝ≥0∞) ∂(alg1Law d ε η p) ≤
          ENNReal.ofReal (expectedBound d ε η)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ ε η : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      η ∈ Set.Ioo (0 : ℝ) (1 / 8) →
        expectedBound d ε η ≤ C * (d : ℝ) ^ 2 / ε ^ 2 * Real.log ((d : ℝ) / η)) := by sorry

end ListReplicableBias.LowerBound.Supplement
