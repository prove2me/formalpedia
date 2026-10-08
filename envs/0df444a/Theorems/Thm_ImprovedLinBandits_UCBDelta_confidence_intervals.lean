-- Prove2me | Theorems.Thm_ImprovedLinBandits_UCBDelta_confidence_intervals
-- name    : ImprovedLinBandits.UCBDelta.confidence_intervals
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:23:42.06509+00:00
-- url     : https://prove2.me/theorems/33903298-5bce-4d7a-9700-c4a9f16fc427
-- title:
--   Lemma 6 — Confidence intervals $|\overline X_{i,t} - \mu_i| \le c_{i,t}$ for all arms and times
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space with a filtration $(\mathcal F_t)_{t \ge 0}$. Consider $d$ arms with means $\mu_1, \dots, \mu_d$. In round $t \ge 1$ an arm $I_t$ that is $\mathcal F_{t-1}$-measurable is played, and the reward $\mu_{I_t} + \eta_t$ is received, where the noise $\eta_t$ is $\mathcal F_t$-measurable and conditionally $1$-sub-Gaussian:
--   $$\mathbf E\left[e^{\lambda \eta_t} \mid \mathcal F_{t-1}\right] \le e^{\lambda^2/2} \qquad \text{for all } \lambda \in \mathbb R .$$
--   The arms $I_t$ may be chosen by any adapted rule. Let $N_{i,t}$ be the number of plays of arm $i$ in rounds $1, \dots, t$, $\overline X_{i,t}$ the average reward of arm $i$ over those rounds, and
--   $$c_{i,t} = \sqrt{\frac{1 + N_{i,t}}{N_{i,t}^2}\left(1 + 2\log\left(\frac{d\,(1 + N_{i,t})^{1/2}}{\delta}\right)\right)} .$$
--   Then for every $\delta > 0$, with probability at least $1 - \delta$,
--   $$|\overline X_{i,t} - \mu_i| \le c_{i,t} \qquad \text{for all arms } i \text{ and all } t \ge 0 \text{ with } N_{i,t} \ge 1 .$$
--
--   The event is uniform in time: a single event of probability at least $1-\delta$ carries all the intervals simultaneously. This is what allows the UCB($\delta$) algorithm to use widths that depend neither on the horizon nor on the current time.
--
--   **Formalization Note** The statement bounds the outer probability of the failure event "$|\overline X_{i,t} - \mu_i| > c_{i,t}$ for some $i$ and some $t$ with $N_{i,t} \ge 1$" by $\delta$. For $N_{i,t} = 0$ the paper's width is $+\infty$ and the inequality is vacuous; Lean's division by zero would give $0$ on both sides, so that case is excluded explicitly. The noise is conditioned on $\mathcal F_{t-1}$, the filtration form of Theorem 1, which is more general than conditioning on $I_{1:t}, \eta_{1:t-1}$. The hypothesis that $\Omega$ is a standard Borel space is added so that Mathlib's conditional sub-Gaussianity (through the conditional distribution kernel) is available; it is not in the paper.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 7, Lemma 6 and eq. (3)

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel

open MeasureTheory ProbabilityTheory

namespace ImprovedLinBandits.UCBDelta

/-- **Lemma 6** (Confidence Intervals; Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011, p. 7). Arms
`Fin d` have means `μ`; round `t + 1` plays the `ℱ_t`-measurable arm `I (t + 1)` and receives
`μ (I (t + 1)) + η (t + 1)`, where `η (t + 1)` is `ℱ_{t+1}`-measurable and conditionally
1-sub-Gaussian given `ℱ_t`. Then for every `δ > 0`, the (outer) probability that
`|X̄_{i,t} - μ_i| > c_{i,t}` for some arm `i` and some `t ≥ 0` is at most `δ`.
The case `N_{i,t} = 0`, where the paper's `c_{i,t} = +∞` makes the claim vacuous, is excluded
explicitly. The arm sequence is arbitrary (not necessarily UCB(δ)). `StandardBorelSpace Ω` is
added so that Mathlib's conditional sub-Gaussianity is available. -/
theorem confidence_intervals
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ)
    (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ (i : Fin d) (t : ℕ), 0 < pullCount I i t ω ∧
        confRadius d δ (pullCount I i t ω) < |empMean μ η I i t ω - μ i|}
      ≤ ENNReal.ofReal δ := by sorry

end ImprovedLinBandits.UCBDelta
