-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_lemma_5
-- name    : FoundationsRL.StatLearning.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:41.02385+00:00
-- url     : https://prove2.me/theorems/737e50fc-2cbb-4ebb-8778-23fd1c007607
-- title:
--   Lemma 5 — Bernstein's inequality
-- statement:
--   Let $Z_1,\dots,Z_T,Z$ be i.i.d. with variance $\mathbb V(Z_i)=\sigma^2$ and range $|Z-\mathbb EZ|\le B$ almost surely. Then for $\delta\in(0,1)$, with probability at least $1-\delta$,
--
--   $$
--   \frac1T\sum_{i=1}^TZ_i-\mathbb EZ\le\sigma\sqrt{\frac{2\log(1/\delta)}{T}}+\frac{B\log(1/\delta)}{3T}.
--   $$
--
--   Compared with Hoeffding's inequality, the leading term scales with the standard deviation rather than the range, which is the source of the fast rate for the square loss.
--
--   **Formalization Note** $\sigma\ge0$ is the root of the variance. This form with the factor $1/3$ in the second term differs from the usual inversion of the Bernstein tail, which gives $2/3$.
--
--   Differences from the source:
--   - encoding: Z₁, …, Z_T i.i.d. with a generic copy Z → Zs mutually independent, each identically distributed with Z; reason: the notes' E[Z] is the common mean
--   - encoding: with probability at least 1 − δ, δ unconstrained → 0 < δ < 1; reason: the range stated at (1.12)
--   - encoding: σ the root of the variance → 0 ≤ σ with Var(Z) = σ²; reason: σ is a standard deviation
--   - encoding: T not stated → T ≥ 1; reason: the sample mean and the bound divide by T
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 5, (1.16), p. 12

import Mathlib
open MeasureTheory ProbabilityTheory

namespace FoundationsRL.StatLearning

/-- **Lemma 5** (Bernstein's inequality). Let `Z₁, …, Z_T, Z` be i.i.d. with variance
`V(Z_i) = σ²` and range `|Z − E Z| ≤ B` almost surely. Then with probability at least `1 − δ`,
`(1/T) ∑ Z_i − E Z ≤ σ √(2 log(1/δ)/T) + B log(1/δ)/(3T)` (1.16).
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Lemma 5, (1.16), p. 12.

**Formalization Note.** `Zs` are i.i.d. copies of `Z`. The notes' `σ` is the nonnegative root of the
variance, hence `0 ≤ σ`. `δ ∈ (0, 1)` as at (1.12). Measurability of `Z` is carried by `IdentDistrib`,
and with the range bound it makes `E Z` and the variance genuine. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (T : ℕ) (hT : 0 < T) (Zs : Fin T → Ω → ℝ) (hindep : iIndepFun Zs μ)
    (hid : ∀ i, IdentDistrib (Zs i) Z μ μ)
    (σ B : ℝ) (hσ : 0 ≤ σ) (hvar : variance Z μ = σ ^ 2)
    (hB : ∀ᵐ ω ∂μ, |Z ω - ∫ ω', Z ω' ∂μ| ≤ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {ω | (1 / (T : ℝ)) * ∑ i, Zs i ω - ∫ ω', Z ω' ∂μ ≤
      σ * Real.sqrt (2 * Real.log (1 / δ) / (T : ℝ)) +
        B * Real.log (1 / δ) / (3 * (T : ℝ))} := by sorry

end FoundationsRL.StatLearning
