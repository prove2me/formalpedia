-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_lemma_3
-- name    : FoundationsRL.StatLearning.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:50.527982+00:00
-- url     : https://prove2.me/theorems/02c8dff1-ea7d-49f0-ae04-da4933735ca5
-- title:
--   Lemma 3 — Hoeffding's lemma and Hoeffding's inequality for sample means
-- statement:
--   Let $Z$ be a random variable taking values in $[a,b]$ almost surely. Then $Z$ is sub-Gaussian with variance proxy $(b-a)^2/4$, that is
--
--   $$
--   \forall\eta\in\mathbb R,\qquad\ln\mathbb E\exp\{-\eta(Z-\mathbb E[Z])\}\le\frac{\eta^2(b-a)^2}{8}.
--   $$
--
--   As a consequence, for i.i.d. $Z_1,\dots,Z_T$ with the law of $Z$ and any $\delta\in(0,1)$, with probability at least $1-\delta$,
--
--   $$
--   \frac1T\sum_{i=1}^TZ_i-\mathbb E[Z]\le(b-a)\sqrt{\frac{\log(1/\delta)}{2T}}.
--   $$
--
--   This is the concentration input to the slow rate of Proposition 1.
--
--   Differences from the source:
--   - encoding: Z₁, …, Z_T i.i.d. with a generic copy Z → Zs mutually independent, each identically distributed with Z; reason: the notes' E[Z] is the common mean
--   - encoding: with probability at least 1 − δ, δ unconstrained → 0 < δ < 1; reason: the range stated at (1.12)
--   - encoding: the lemma ends with the unfinished sentence "In particular, in the setting of Section 1.4," → omitted; reason: the sentence states nothing
--   - encoding: T not stated → T ≥ 1; reason: the sample mean and the bound divide by T
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 3, (1.13)–(1.14), p. 11

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubGaussian
open MeasureTheory ProbabilityTheory

namespace FoundationsRL.StatLearning

/-- **Lemma 3** (Hoeffding's inequality). Any random variable `Z` taking values in `[a, b]` is
sub-Gaussian with variance proxy `(b − a)²/4`, i.e. `ln E exp(−η(Z − E[Z])) ≤ η²(b − a)²/8` for all
`η ∈ ℝ` (1.13). As a consequence, for i.i.d. `Z₁, …, Z_T` with values in `[a, b]` almost surely, with
probability at least `1 − δ`, `(1/T) ∑ Z_i − E[Z] ≤ (b − a) √(log(1/δ)/(2T))` (1.14).
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Lemma 3, (1.13)–(1.14), p. 11.

**Formalization Note.** The variance proxy `(b − a)²/4` is the square of the parameter `σ = (b − a)/2`
of `IsSubGaussian`. `Zs` are i.i.d. copies of `Z`; `δ ∈ (0, 1)` as at (1.12). The set of
outcomes is measured with `μ.real`. The sentence "In particular, in the setting of Section 1.4,"
that ends the lemma on p. 11 is unfinished in the source and carries no statement. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : AEMeasurable Z μ) (a b : ℝ) (hab : ∀ᵐ ω ∂μ, Z ω ∈ Set.Icc a b) :
    HighDimStat.TailBounds.IsSubGaussian Z μ ((b - a) / 2) ∧
    (∀ η : ℝ, Real.log (∫ ω, Real.exp (-η * (Z ω - ∫ ω', Z ω' ∂μ)) ∂μ) ≤ η ^ 2 * (b - a) ^ 2 / 8) ∧
    ∀ (T : ℕ) (hT : 0 < T) (Zs : Fin T → Ω → ℝ) (hindep : iIndepFun Zs μ) (hid : ∀ i, IdentDistrib (Zs i) Z μ μ)
      (δ : ℝ), 0 < δ → δ < 1 →
      1 - δ ≤ μ.real {ω | (1 / (T : ℝ)) * ∑ i, Zs i ω - ∫ ω', Z ω' ∂μ ≤
        (b - a) * Real.sqrt (Real.log (1 / δ) / (2 * (T : ℝ)))} := by sorry

end FoundationsRL.StatLearning
