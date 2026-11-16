-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_lemma_6_5
-- name    : ListReplicableBias.LowerBound.Supplement.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:59.642171+00:00
-- url     : https://prove2.me/theorems/74b7dd14-e3c1-49e4-9902-350e04ecc6cd
-- title:
--   Lemma 6.5 — a uniform shift fails to be α-good with probability exactly 2α/ε
-- statement:
--   Let $\alpha\in(0,\varepsilon/2]$ and let $U\sim\mathrm{Unif}([0,\varepsilon))$.
--   1. For every $p\in[0,1]$,
--   $$\Pr_U\big(U\text{ is not }\alpha\text{-good for }p\big)=\frac{2\alpha}{\varepsilon}.$$
--   2. The same equality holds when $p$ is a random variable with values in $[0,1]$, independent of $U$.
--
--   This exact failure probability bounds the bad-shift event of Lemma 6.10 and the probability that a coin stays active in Lemma 6.12.
--
--   Differences from the source:
--   - encoding: a random p ∈ [0, 1] independent of U → an arbitrary probability measure ν on ℝ with ν([0, 1]ᶜ) = 0, and the product law ν ⊗ Unif([0, ε)); reason: independence means the joint law is the product of the marginals
--   - encoding: Unif([0, ε)) and probabilities → Lebesgue measure conditioned on [0, ε); probabilities as ℝ≥0∞ masses equal to ENNReal.ofReal (2α/ε); reason: the same law; 2α/ε ∈ (0, 1] so no truncation occurs
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 6.5, PDF pp. 8–9

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Lemma 6.5, PDF p. 8, both clauses, as equalities. Clause 2: p is a random
variable with values in [0, 1] (law ν) independent of U (product law). -/
theorem lemma_6_5 (ε α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) (ε / 2)) :
    (∀ p ∈ Set.Icc (0 : ℝ) 1,
      uniformShift ε {u | ¬ IsGoodShift ε α p u} = ENNReal.ofReal (2 * α / ε)) ∧
    (∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      (ν.prod (uniformShift ε)) {z : ℝ × ℝ | ¬ IsGoodShift ε α z.1 z.2} =
        ENNReal.ofReal (2 * α / ε)) := by sorry

end ListReplicableBias.LowerBound.Supplement
