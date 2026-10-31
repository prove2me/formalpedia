-- Prove2me | Theorems.Thm_FoundationsRL_StatLearning_lemma_2
-- name    : FoundationsRL.StatLearning.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:01.392991+00:00
-- url     : https://prove2.me/theorems/02280269-7f15-4469-a40c-f8cdd2994fc8
-- title:
--   Lemma 2 — sub-Gaussian sample mean tail
-- statement:
--   Let $Z_1,\dots,Z_T$ be i.i.d. sub-Gaussian random variables with variance proxy $\sigma^2>0$, and let $Z$ have their common law. Then for every $u\ge0$,
--
--   $$
--   \mathbb P\Big(\frac1T\sum_{i=1}^TZ_i-\mathbb E[Z]\ge u\Big)\le\exp\Big(-\frac{Tu^2}{2\sigma^2}\Big).
--   $$
--
--   Sample means of sub-Gaussian variables thus concentrate at the Gaussian rate $\sigma/\sqrt T$.
--
--   Differences from the source:
--   - reading: u unrestricted → u ≥ 0; reason: the bound is false for u < 0, where its right side is below 1 and the left side tends to 1 as u → −∞
--   - encoding: σ² any variance proxy → σ² > 0; reason: the right side divides by σ²; only the undefined case is excluded
--   - encoding: Z₁, …, Z_T i.i.d. with a generic copy Z → Zs mutually independent, each identically distributed with Z; reason: the notes' E[Z] is the common mean
--   - encoding: T not stated → T ≥ 1; reason: the sample mean and the bound divide by T
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 2, (1.10), p. 10

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubGaussian
open MeasureTheory ProbabilityTheory

namespace FoundationsRL.StatLearning

/-- **Lemma 2** (sub-Gaussian sample mean tail). If `Z₁, …, Z_T` are i.i.d. sub-Gaussian with
variance proxy `σ²`, then `P((1/T) ∑ Z_i − E[Z] ≥ u) ≤ exp(−Tu²/(2σ²))` (1.10).
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Lemma 2, (1.10), p. 10.

**Formalization Note.** `Zs` are i.i.d. copies of `Z`, and `σ²` is the variance proxy of `IsSubGaussian Z μ σ`. The bound is for `u ≥ 0`: the notes leave the
range of `u` implicit, and it fails for `u < 0` (its right side is below `1`, and the left side tends
to `1` as `u → −∞`). `σ² > 0` is assumed because the right side divides by it; `σ² = 0` is the
degenerate constant case. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hsub : HighDimStat.TailBounds.IsSubGaussian Z μ σ)
    (T : ℕ) (hT : 0 < T) (Zs : Fin T → Ω → ℝ) (hindep : iIndepFun Zs μ)
    (hid : ∀ i, IdentDistrib (Zs i) Z μ μ) (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ (1 / (T : ℝ)) * ∑ i, Zs i ω - ∫ ω', Z ω' ∂μ} ≤
      Real.exp (-((T : ℝ) * u ^ 2 / (2 * σ ^ 2))) := by sorry

end FoundationsRL.StatLearning
