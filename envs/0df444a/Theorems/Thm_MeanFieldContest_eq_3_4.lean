-- Prove2me | Theorems.Thm_MeanFieldContest_eq_3_4
-- name    : MeanFieldContest.eq_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:57.519432+00:00
-- url     : https://prove2.me/theorems/a2edc544-0367-42c5-b36a-424b23074dda
-- title:
--   (3.4) — $\bar R=u^{F^*}(x_0)=\min_{F\in\mathcal F}u^F(x_0)$ at an equilibrium $F^*$
-- statement:
--   Let $R$ be a reward function, $\mu<\bar\mu_\infty$, and let $F^*$ be any mean field equilibrium. Then
--   $$\bar R=u^{F^*}(x_0)=\min_{F\in\mathcal F}u^F(x_0).$$
--
--   In words: in equilibrium the opposing players act so as to minimize the value of a representative player, and that minimum is the average reward.
--
--   Differences from the source:
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: min over 𝓕 attained at F* → u^{F*}(x₀) = R̄ with F* ∈ 𝓕, and R̄ ≤ u^F(x₀) for all F ∈ 𝓕; reason: this is the definition of the minimum
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, (3.4), p.12

import Mathlib
import Definitions.Def_MeanFieldContest_Model

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **(3.4)**, arXiv:2103.04219v1, p.12. If `F*` is an equilibrium, then `R̄ = u^{F*}(x₀) = min_{F ∈ 𝓕} u^F(x₀)`.

**Formalization Note.** Here `Fs` is any equilibrium (the paper's `F*` in this display is not yet the
formula (2.3)). The minimum is stated as: the value at `Fs ∈ 𝓕` is `R̄`, and `R̄` is a lower bound of
`u^F(x₀)` on `𝓕`. -/
theorem eq_3_4 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {Fs : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ)
    (hF : IsMFE x₀ μ σ R Fs) :
    valueFn μ σ R Fs x₀ = Rbar R ∧
      ∀ F ∈ feasibleLaws x₀ μ σ, Rbar R ≤ valueFn μ σ R F x₀ := by sorry

end MeanFieldContest
