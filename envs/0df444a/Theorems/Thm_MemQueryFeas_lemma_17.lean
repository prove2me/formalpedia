-- Prove2me | Theorems.Thm_MemQueryFeas_lemma_17
-- name    : MemQueryFeas.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:32:43.11739+00:00
-- url     : https://prove2.me/theorems/c6d663d8-dfdc-49a9-8f48-aaf7d246f9d1
-- title:
--   Lemma 17 — expected inverse threshold
-- statement:
--   Let $X$ be a random variable with values in $[0,1]$ and $\mathbb E[X]\ge\alpha$ for some $\alpha\in(0,1]$. Then there is $x^*\in(0,1]$ such that
--   $$
--   \Pr(X\ge x^*)\ge\frac{\alpha}{3x^*\ln(3/\alpha)}\qquad\text{and}\qquad x^*\ge\frac{\alpha}{3\ln(3/\alpha)} .
--   $$
--
--   This elementary estimate converts an expected success probability into a threshold event of non-negligible probability; it is used in the proof of Proposition 2.
--
--   Differences from the source: none.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 17, p.38 (PDF p.39)

import Mathlib

open MeasureTheory

namespace MemQueryFeas

/-- **Lemma 17 (expected inverse threshold).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 17, p.38 (PDF p.39): "Let `X ∈ [0, 1]` be a
random variable with `E[X] ≥ α ∈ (0, 1]`. Then there exists `x∗ ∈ (0, 1]`, such that
`P(X ≥ x∗) ≥ α/(3x∗ ln(3/α))` and `x∗ ≥ α/(3 ln(3/α))`."

**Formalization Note.** `X` is measurable on a probability space with values in `[0,1]` (hence
integrable). `ln` is the natural logarithm. -/
theorem lemma_17 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX01 : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hE : α ≤ ∫ ω, X ω ∂μ) :
    ∃ x : ℝ, 0 < x ∧ x ≤ 1 ∧
      ENNReal.ofReal (α / (3 * x * Real.log (3 / α))) ≤ μ {ω | x ≤ X ω} ∧
      α / (3 * Real.log (3 / α)) ≤ x := by sorry

end MemQueryFeas
